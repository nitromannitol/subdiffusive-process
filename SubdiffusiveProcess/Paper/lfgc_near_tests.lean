import SubdiffusiveProcess.Paper.lfgc_err_compare

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Near-unit charts pass the single-point tests; nearness transfers between close charts

`aux_lfgc_near_tests_NearChart σ F ref θ`: the normalized inverse lower ellipticity, upper ellipticity,
top-cube `σ` entries and homogenization error of the chart `F` (reference `ref`) are within
`θ` of their unit values `1, 1, δ_ij, 0`.  For `θ ≤ 1/(4d)` this gives the ellipticity window
`[2/3, 3/2]`, the coercivity with constant `1/(2d)` and the error bound `θ`.
If `aux_lfgc_chart_compare_ChartsClose F F' κ ε`, nearness passes to `F'` with reference `κ ref` and tolerance
`θ' ε θ = max (e^ε (1+θ) - 1) (√(e^ε θ² + e^ε - 1))`.  Deterministic.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02
open scoped ENNReal

namespace Paper
variable {d : ℕ}

/-- The transferred tolerance. -/
noncomputable def aux_lfgc_near_tests_tolTransfer (ε θ : ℝ) : ℝ :=
  max (Real.exp ε * (1 + θ) - 1) (Real.sqrt (Real.exp ε * θ ^ 2 + (Real.exp ε - 1)))

/-- The chart quantities are within `θ` of their unit values. -/
def aux_lfgc_near_tests_NearChart (σ : ℝ) (F : TriadicCoeffFamily d) (ref θ : ℝ) : Prop :=
  |ref / Paper.aux_lem_band_U2_lamF σ F - 1| ≤ θ ∧
  |Paper.aux_lem_band_U2_LamF σ F / ref - 1| ≤ θ ∧
  (∀ i j : Fin d, |Paper.aux_lem_band_U2_sigF i j F / ref - (if i = j then (1 : ℝ) else 0)| ≤ θ) ∧
  Paper.aux_lem_band_U2_errF σ F ref ≤ θ

theorem aux_lfgc_near_tests_exp_add_exp_neg_ge_two (ε : ℝ) : 2 ≤ Real.exp ε + Real.exp (-ε) := by
  have hu := Real.exp_pos ε
  rw [Real.exp_neg]
  have : 0 ≤ (Real.exp ε - 1) ^ 2 / Real.exp ε := div_nonneg (sq_nonneg _) hu.le
  have e : (Real.exp ε - 1) ^ 2 / Real.exp ε = Real.exp ε + (Real.exp ε)⁻¹ - 2 := by
    field_simp; ring
  linarith

/-- Multiplicative perturbation of a quantity near one. -/
theorem aux_lfgc_near_tests_ratio_transfer {y y' ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 ≤ θ)
    (hlo : Real.exp (-ε) * y ≤ y') (hhi : y' ≤ Real.exp ε * y) (hy : |y - 1| ≤ θ) :
    |y' - 1| ≤ Real.exp ε * (1 + θ) - 1 := by
  have h1 := abs_le.mp hy
  have he := Real.exp_pos ε
  have hen := Real.exp_pos (-ε)
  have h2 := aux_lfgc_near_tests_exp_add_exp_neg_ge_two ε
  have hmul : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
  rw [abs_le]
  constructor
  · have : Real.exp (-ε) * (1 - θ) ≤ y' := le_trans (by nlinarith) hlo
    have hexp1 : 1 ≤ Real.exp ε := Real.one_le_exp hε
    have hexpn : Real.exp (-ε) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  · nlinarith

theorem aux_lfgc_near_tests_quad_polarization (A : Mat d) (hA : A.IsSymm) (i j : Fin d) :
    A i j = (vecDot (Pi.single i 1 + Pi.single j 1) (matVecMul A (Pi.single i 1 + Pi.single j 1)) -
      vecDot (Pi.single i 1 - Pi.single j 1) (matVecMul A (Pi.single i 1 - Pi.single j 1))) / 4 := by
  have hs : A j i = A i j := by
    have := congrFun (congrFun hA i) j
    simpa [Matrix.transpose_apply] using this
  have key : ∀ (v : Vec d), vecDot v (matVecMul A v) = ∑ a, ∑ b, v a * A a b * v b := by
    intro v; unfold vecDot matVecMul
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [key, key]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  have e1 : ∀ a b : Fin d, ((if a = i then (1:ℝ) else 0) + (if a = j then 1 else 0)) * A a b *
      ((if b = i then 1 else 0) + (if b = j then 1 else 0)) -
      ((if a = i then (1:ℝ) else 0) - (if a = j then 1 else 0)) * A a b *
      ((if b = i then 1 else 0) - (if b = j then 1 else 0)) =
      2 * ((if a = i then (1:ℝ) else 0) * A a b * (if b = j then 1 else 0)) +
      2 * ((if a = j then (1:ℝ) else 0) * A a b * (if b = i then 1 else 0)) := by
    intro a b; ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, e1, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, one_mul, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [hs]; ring

/-- Entry perturbation under a Loewner sandwich `e^{-ε} A ≤ A' ≤ e^{ε} A`. -/
theorem lfgc_near_tests (A A' : Mat d) (hA : A.IsSymm) (hA' : A'.IsSymm)
    (hpos : ∀ v, 0 ≤ vecDot v (matVecMul A v)) {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 ≤ θ)
    (hhi : ∀ v, vecDot v (matVecMul A' v) ≤ Real.exp ε * vecDot v (matVecMul A v))
    (hlo : ∀ v, Real.exp (-ε) * vecDot v (matVecMul A v) ≤ vecDot v (matVecMul A' v))
    (hnear : ∀ i j, |A i j - (if i = j then (1 : ℝ) else 0)| ≤ θ) (i j : Fin d) :
    |A' i j - (if i = j then (1 : ℝ) else 0)| ≤ Real.exp ε * (1 + θ) - 1 := by
  set M : Mat d := A' - A
  have hM : M.IsSymm := by
    unfold Matrix.IsSymm at *; simp only [M, Matrix.transpose_sub, hA, hA']
  have hqM : ∀ v, vecDot v (matVecMul M v) = vecDot v (matVecMul A' v) - vecDot v (matVecMul A v) := by
    intro v; unfold vecDot matVecMul M
    simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
  have hexp1 : 1 ≤ Real.exp ε := Real.one_le_exp hε
  have hexpn : 1 - Real.exp (-ε) ≤ Real.exp ε - 1 := by
    have := aux_lfgc_near_tests_exp_add_exp_neg_ge_two ε; linarith
  have hbound : ∀ v, |vecDot v (matVecMul M v)| ≤ (Real.exp ε - 1) * vecDot v (matVecMul A v) := by
    intro v
    rw [hqM, abs_le]
    have h1 := hhi v; have h2 := hlo v; have h3 := hpos v
    constructor <;> nlinarith
  have hpolM := aux_lfgc_near_tests_quad_polarization M hM i j
  have hpolA_plus : vecDot (Pi.single i 1 + Pi.single j 1)
      (matVecMul A (Pi.single i 1 + Pi.single j 1)) +
      vecDot (Pi.single i 1 - Pi.single j 1) (matVecMul A (Pi.single i 1 - Pi.single j 1)) =
      2 * (A i i + A j j) := by
    have key : ∀ (v : Vec d), vecDot v (matVecMul A v) = ∑ a, ∑ b, v a * A a b * v b := by
      intro v; unfold vecDot matVecMul
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [key, key, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib]
    have e1 : ∀ a b : Fin d, (Pi.single i (1:ℝ) + Pi.single j 1 : Vec d) a * A a b *
        (Pi.single i (1:ℝ) + Pi.single j 1 : Vec d) b +
        (Pi.single i (1:ℝ) - Pi.single j 1 : Vec d) a * A a b *
        (Pi.single i (1:ℝ) - Pi.single j 1 : Vec d) b =
        2 * ((Pi.single i (1:ℝ) : Vec d) a * A a b * (Pi.single i (1:ℝ) : Vec d) b) +
        2 * ((Pi.single j (1:ℝ) : Vec d) a * A a b * (Pi.single j (1:ℝ) : Vec d) b) := by
      intro a b; simp only [Pi.add_apply, Pi.sub_apply]; ring
    simp_rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Pi.single_apply, ite_mul, zero_mul, mul_ite, mul_zero, one_mul, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hMij : |M i j| ≤ (Real.exp ε - 1) * (A i i + A j j) / 2 := by
    rw [hpolM]
    have b1 := hbound (Pi.single i 1 + Pi.single j 1)
    have b2 := hbound (Pi.single i 1 - Pi.single j 1)
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    have := abs_sub _ _ |>.trans (add_le_add b1 b2)
    rw [← mul_add, hpolA_plus] at this
    linarith
  have hii := abs_le.mp (hnear i i)
  have hjj := abs_le.mp (hnear j j)
  simp only [if_true] at hii hjj
  have hsum : A i i + A j j ≤ 2 * (1 + θ) := by linarith
  have hMij' : |M i j| ≤ (Real.exp ε - 1) * (1 + θ) := by
    refine hMij.trans ?_
    have := mul_le_mul_of_nonneg_left hsum (by linarith : (0:ℝ) ≤ Real.exp ε - 1)
    linarith
  have hA'eq : A' i j = A i j + M i j := by simp [M]
  rw [hA'eq]
  calc |A i j + M i j - (if i = j then (1 : ℝ) else 0)|
      = |(A i j - (if i = j then (1 : ℝ) else 0)) + M i j| := by ring_nf
    _ ≤ |A i j - (if i = j then (1 : ℝ) else 0)| + |M i j| := abs_add_le _ _
    _ ≤ θ + (Real.exp ε - 1) * (1 + θ) := add_le_add (hnear i j) hMij'
    _ = Real.exp ε * (1 + θ) - 1 := by ring

end Paper
