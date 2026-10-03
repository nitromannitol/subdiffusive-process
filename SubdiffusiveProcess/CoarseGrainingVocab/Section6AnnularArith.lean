module

public import Homogenization.Book.Ch02.MultiscaleEllipticity

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization.Book

open scoped BigOperators ENNReal

noncomputable section

/-! ## Real geometric weights as `ℝ≥0∞` powers -/

/-- A real power of `3` with a natural multiple in the exponent is an
`ℝ≥0∞` power. -/
private theorem ofReal_rpow_natMul (a : ℝ) (l : ℕ) :
    ENNReal.ofReal ((3 : ℝ) ^ (a * (l : ℝ))) =
      ENNReal.ofReal ((3 : ℝ) ^ a) ^ l := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast,
    ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) a)]

/-- The geometric series `∑ 3^{-a l}` in `ℝ≥0∞`. -/
private theorem tsum_ofReal_rpow_geometric (a : ℝ) :
    ∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-a * (l : ℝ))) =
      (1 - ENNReal.ofReal ((3 : ℝ) ^ (-a)))⁻¹ := by
  simp only [ofReal_rpow_natMul]
  exact ENNReal.tsum_geometric _

/-- `1 - 3^{-a}` as an `ℝ≥0∞` subtraction. -/
private theorem one_sub_ofReal_rpow_neg (a : ℝ) :
    1 - ENNReal.ofReal ((3 : ℝ) ^ (-a)) =
      ENNReal.ofReal (1 - (3 : ℝ) ^ (-a)) := by
  rw [ENNReal.ofReal_sub _ (Real.rpow_nonneg (by norm_num) _), ENNReal.ofReal_one]

/-- If a nonnegative real `c` is at most `κ` times `1 - 3^{-a}`, then the
`ℝ≥0∞` product of `c` with the geometric sum `(1 - 3^{-a})⁻¹` is at most `κ`. -/
private theorem ofReal_mul_geometric_le {a c κ : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ)
    (hc : c ≤ κ * (1 - (3 : ℝ) ^ (-a))) :
    ENNReal.ofReal c * (1 - ENNReal.ofReal ((3 : ℝ) ^ (-a)))⁻¹ ≤
      ENNReal.ofReal κ := by
  have hlt : (3 : ℝ) ^ (-a) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-a) := by linarith
  set b : ℝ≥0∞ := 1 - ENNReal.ofReal ((3 : ℝ) ^ (-a)) with hb
  have hbeq : b = ENNReal.ofReal (1 - (3 : ℝ) ^ (-a)) := one_sub_ofReal_rpow_neg a
  have hb0 : b ≠ 0 := by
    rw [hbeq]
    exact (ENNReal.ofReal_pos.2 hpos).ne'
  have hbtop : b ≠ ⊤ := by rw [hbeq]; exact ENNReal.ofReal_ne_top
  have hstep : ENNReal.ofReal c ≤ ENNReal.ofReal κ * b := by
    rw [hbeq, ← ENNReal.ofReal_mul hκ]
    exact ENNReal.ofReal_le_ofReal hc
  calc ENNReal.ofReal c * b⁻¹
      ≤ (ENNReal.ofReal κ * b) * b⁻¹ := by gcongr
    _ = ENNReal.ofReal κ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hb0 hbtop, mul_one]

/-! ## The elementary scalar estimates -/

/-- The `q = 2` geometric discount is at most four times the `s/2` discount:
`1 - x⁴ = (1 - x)(1 + x + x² + x³) ≤ 4 (1 - x)` at `x = 3^{-s/2}`. -/
theorem geometricDiscount_two_le_four_mul {s : ℝ} (hs : 0 ≤ s) :
    Ch02.geometricDiscount s 2 ≤ 4 * (1 - (3 : ℝ) ^ (-(s / 2))) := by
  set x : ℝ := (3 : ℝ) ^ (-(s / 2)) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hpow : Real.rpow (3 : ℝ) (-s * 2) = x ^ (4 : ℕ) := by
    rw [hx, ← Real.rpow_natCast ((3 : ℝ) ^ (-(s / 2))) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hdisc : Ch02.geometricDiscount s 2 = 1 - x ^ (4 : ℕ) := by
    rw [Ch02.geometricDiscount, hpow]
  rw [hdisc]
  nlinarith [sq_nonneg x, sq_nonneg (1 - x), sq_nonneg (x * x)]

/-- `3^{3s/2} ≤ 3` for `s ≤ 1/2`. -/
private theorem rpow_three_halves_le_three {s : ℝ} (hs2 : s ≤ 1 / 2) :
    (3 : ℝ) ^ (3 * s / 2) ≤ 3 := by
  calc (3 : ℝ) ^ (3 * s / 2) ≤ (3 : ℝ) ^ (1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        linarith
    _ = 3 := Real.rpow_one 3

/-- `3^{-(D - 3s/2)} ≤ 4/5` whenever `1 ≤ D` and `s ≤ 1/2`; this gives the
uniform bound `5` on the inner geometric sum. -/
private theorem rpow_neg_gap_le {s D : ℝ} (hs2 : s ≤ 1 / 2) (hD : 1 ≤ D) :
    (3 : ℝ) ^ (-(D - 3 * s / 2)) ≤ 4 / 5 := by
  have hquarter : (3 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 4 / 5 := by
    have h4 : ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ (4 : ℕ) = (3 : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 4 : ℝ))) 4,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        show (-(1 / 4 : ℝ)) * ((4 : ℕ) : ℝ) = -1 by norm_num,
        Real.rpow_neg_one]
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by norm_num) ?_
    rw [h4]
    norm_num
  refine le_trans ?_ hquarter
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  linarith

/-- Powers of `3` multiply. -/
private theorem ofReal_rpow_mul_ofReal_rpow (a b : ℝ) :
    ENNReal.ofReal ((3 : ℝ) ^ a) * ENNReal.ofReal ((3 : ℝ) ^ b) =
      ENNReal.ofReal ((3 : ℝ) ^ (a + b)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) a),
    ← Real.rpow_add (by norm_num)]

/-! ## The resummation -/

/-- **Annular resummation, arithmetic core.**

`A l` is the scale-`m - l` grid maximum, split into an annular part `Ann l` and
a central part `Cen l`.  The annular part is dominated by the annular supremum
`K` at the weaker discount `3^{-(3/2)s(m-n)}`; the central part is dominated by
a `3^{-D}`-summable family whose scale-`m - l - 1 - t` entries are themselves
dominated by `K`.  The conclusion is the manuscript's
`e.mathcalE.annular.decomp.pre` with an explicit absolute constant.

The manuscript proves this by interchanging the two summations; here the
annular supremum is pushed through the inner sum first, after which the two
geometric series factor and no interchange is needed. -/
theorem tsum_geometricWeight_le_of_annular_split
    {s D : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (hD : 1 ≤ D)
    {A Ann Cen : ℕ → ℝ≥0∞} {Y : ℕ → ℕ → ℝ≥0∞} {K : ℝ≥0∞}
    (hA : ∀ l, A l ≤ Ann l + Cen l)
    (hAnn : ∀ l, Ann l ≤ ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * (l : ℝ))) * K)
    (hCen : ∀ l, Cen l ≤
      ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-D * (t : ℝ))) * Y l t)
    (hY : ∀ l t, Y l t ≤
      ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((l : ℝ) + 1 + (t : ℝ)))) * K) :
    ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) * A l ≤ 64 * K := by
  have hgap : 0 < D - 3 * s / 2 := by linarith
  set gd : ℝ := Ch02.geometricDiscount s 2 with hgd
  have hgd0 : 0 ≤ gd := by
    have hle1 : Real.rpow (3 : ℝ) (-s * 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    rw [hgd, Ch02.geometricDiscount]
    linarith
  set x : ℝ≥0∞ := (1 - ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2))))⁻¹ with hx
  set y : ℝ≥0∞ := (1 - ENNReal.ofReal ((3 : ℝ) ^ (-(D - 3 * s / 2))))⁻¹ with hy
  -- the weight splits off the discount
  have hgwsplit : ∀ l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) =
      ENNReal.ofReal gd * ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) := by
    intro l
    have hexp : Real.rpow (3 : ℝ) (-s * 2 * (l : ℝ)) =
        (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) := by
      congr 1
      ring
    rw [Ch02.geometricWeight, hexp, ← ENNReal.ofReal_mul hgd0, hgd]
  -- the annular part
  have hT1 : ∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) * Ann l ≤
      x * K := by
    calc ∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) * Ann l
        ≤ ∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) *
            (ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * (l : ℝ))) * K) :=
          ENNReal.tsum_le_tsum fun l => by gcongr; exact hAnn l
      _ = ∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * (l : ℝ))) * K := by
          refine tsum_congr fun l => ?_
          have he : -(2 * s) * (l : ℝ) + 3 * s / 2 * (l : ℝ) =
              -(s / 2) * (l : ℝ) := by ring
          rw [← mul_assoc, ofReal_rpow_mul_ofReal_rpow, he]
      _ = (∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * (l : ℝ)))) * K :=
          ENNReal.tsum_mul_right
      _ = x * K := by rw [tsum_ofReal_rpow_geometric, hx]
  -- the central part
  have hT2inner : ∀ l : ℕ,
      ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-D * (t : ℝ))) * Y l t ≤
        ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((l : ℝ) + 1))) * y * K := by
    intro l
    calc ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-D * (t : ℝ))) * Y l t
        ≤ ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-D * (t : ℝ))) *
            (ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((l : ℝ) + 1 + (t : ℝ)))) *
              K) := ENNReal.tsum_le_tsum fun t => by gcongr; exact hY l t
      _ = ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(D - 3 * s / 2) * (t : ℝ))) *
            (ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((l : ℝ) + 1))) * K) := by
          refine tsum_congr fun t => ?_
          have he : -D * (t : ℝ) + 3 * s / 2 * ((l : ℝ) + 1 + (t : ℝ)) =
              -(D - 3 * s / 2) * (t : ℝ) + 3 * s / 2 * ((l : ℝ) + 1) := by ring
          rw [← mul_assoc, ← mul_assoc, ofReal_rpow_mul_ofReal_rpow,
            ofReal_rpow_mul_ofReal_rpow, he]
      _ = (∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(D - 3 * s / 2) * (t : ℝ)))) *
            (ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((l : ℝ) + 1))) * K) :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((l : ℝ) + 1))) * y * K := by
          rw [tsum_ofReal_rpow_geometric, hy]
          ring
  have hT2 : ∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) * Cen l ≤
      ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) * y * x * K := by
    calc ∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) * Cen l
        ≤ ∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) *
            (ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((l : ℝ) + 1))) * y * K) :=
          ENNReal.tsum_le_tsum fun l => by
            gcongr
            exact (hCen l).trans (hT2inner l)
      _ = ∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * (l : ℝ))) *
            (ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) * y * K) := by
          refine tsum_congr fun l => ?_
          have he : -(2 * s) * (l : ℝ) + 3 * s / 2 * ((l : ℝ) + 1) =
              -(s / 2) * (l : ℝ) + 3 * s / 2 := by ring
          calc ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) *
                (ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((l : ℝ) + 1))) * y * K)
              = (ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) *
                  ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((l : ℝ) + 1)))) *
                  (y * K) := by ring
            _ = ENNReal.ofReal
                  ((3 : ℝ) ^ (-(s / 2) * (l : ℝ) + 3 * s / 2)) * (y * K) := by
                rw [ofReal_rpow_mul_ofReal_rpow, he]
            _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * (l : ℝ))) *
                  (ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) * y * K) := by
                rw [← ofReal_rpow_mul_ofReal_rpow]
                ring
      _ = (∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * (l : ℝ)))) *
            (ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) * y * K) :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) * y * x * K := by
          rw [tsum_ofReal_rpow_geometric, hx]
          ring
  -- assemble
  have hsplit : ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) * A l ≤
      ENNReal.ofReal gd *
        (x * K + ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) * y * x * K) := by
    calc ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) * A l
        = ENNReal.ofReal gd *
            ∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) * A l := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun l => by rw [hgwsplit l, mul_assoc]
      _ ≤ ENNReal.ofReal gd *
            ((∑' l : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) * Ann l) +
              ∑' l : ℕ,
                ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) * Cen l) := by
          gcongr
          rw [← ENNReal.tsum_add]
          refine ENNReal.tsum_le_tsum fun l => ?_
          calc ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) * A l
              ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(2 * s) * (l : ℝ))) *
                  (Ann l + Cen l) := by gcongr; exact hA l
            _ = _ := mul_add _ _ _
      _ ≤ _ := by gcongr
  refine hsplit.trans ?_
  have h4 : ENNReal.ofReal gd * x ≤ 4 := by
    have := ofReal_mul_geometric_le (a := s / 2) (c := gd) (κ := 4)
      (by linarith) (by norm_num) (geometricDiscount_two_le_four_mul hs.le)
    simpa [hx] using this
  have h5 : y ≤ 5 := by
    have hnum : (1 : ℝ) ≤ 5 * (1 - (3 : ℝ) ^ (-(D - 3 * s / 2))) := by
      have := rpow_neg_gap_le (s := s) (D := D) hs2 hD
      linarith
    have := ofReal_mul_geometric_le (a := D - 3 * s / 2) (c := 1) (κ := 5)
      hgap (by norm_num) hnum
    simpa [hy] using this
  have h3 : ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) ≤ 3 := by
    have := ENNReal.ofReal_le_ofReal (rpow_three_halves_le_three hs2)
    simpa using this
  calc ENNReal.ofReal gd *
        (x * K + ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) * y * x * K)
      = (ENNReal.ofReal gd * x) * K +
          (ENNReal.ofReal gd * x) *
            (ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) * y) * K := by ring
    _ ≤ 4 * K + 4 * ((3 : ℝ≥0∞) * 5) * K := by gcongr
    _ = 64 * K := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab
