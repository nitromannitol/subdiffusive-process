import SubdiffusiveProcess.Lane3.Elementary
import SubdiffusiveProcess.Lane3.Forms
import Mathlib.Tactic




open Finset

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

/-- Lemma `mfd:lem-common`, `eq:mfd-29`, final step (paper line 3345).
`Ez = E^g(z)`; the three nonnegative coefficients `A1, A2, A3` are the three
Cauchy--Schwarz factors of paper lines 3339-3344, each already divided by
`√(E^g(z))`. -/
theorem weighted_difference_energy_bound (m Ez A1 A2 A3 : ℝ) (hm : 0 < m)
    (hEz : 0 ≤ Ez) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3)
    (hbound : m * Ez ≤ (A1 + A2 + A3) * Real.sqrt Ez) :
    Ez ≤ 3 * (A1 ^ 2 + A2 ^ 2 + A3 ^ 2) / m ^ 2 := by
  have hs : Real.sqrt Ez ^ 2 = Ez := Real.sq_sqrt hEz
  have hsnn : 0 ≤ Real.sqrt Ez := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hsnn with h0 | h0
  · have : Ez = 0 := by rw [← hs, ← h0]; ring
    rw [this]
    positivity
  · have hstep : m * Real.sqrt Ez ≤ A1 + A2 + A3 := by
      have hE : m * (Real.sqrt Ez * Real.sqrt Ez) ≤ (A1 + A2 + A3) * Real.sqrt Ez := by
        have hsq : Real.sqrt Ez * Real.sqrt Ez = Ez := Real.mul_self_sqrt hEz
        rw [hsq]
        exact hbound
      nlinarith [hE, h0]
    have hsq2 : (m * Real.sqrt Ez) ^ 2 ≤ (A1 + A2 + A3) ^ 2 := by
      have hnn : 0 ≤ m * Real.sqrt Ez := mul_nonneg hm.le hsnn
      exact pow_le_pow_left₀ hnn hstep 2
    have hexp : (m * Real.sqrt Ez) ^ 2 = m ^ 2 * Ez := by
      rw [mul_pow, hs]
    rw [hexp] at hsq2
    have hcs : (A1 + A2 + A3) ^ 2 ≤ 3 * (A1 ^ 2 + A2 ^ 2 + A3 ^ 2) := by
      nlinarith [sq_nonneg (A1 - A2), sq_nonneg (A1 - A3), sq_nonneg (A2 - A3)]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsq2, hcs]

/-- Lemma `mfd:lem-relvar`, paper line 3388: a quantity bounded by two
nonnegative quantities is bounded by their geometric mean. -/
theorem le_sqrt_mul_of_le_of_le {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxa : x ≤ a) (hxb : x ≤ b) : x ≤ Real.sqrt (a * b) := by
  have hmin : x ≤ min a b := le_min hxa hxb
  exact hmin.trans (min_le_sqrt_mul ha hb)

/-- Lemma `mfd:lem-mass`, paper line 3652: a finite average exceeding `c` has
a summand exceeding `c`. -/
theorem exists_index_gt_of_average_gt {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (c : ℝ) (havg : c * (s.card : ℝ) < ∑ i ∈ s, f i) :
    ∃ i ∈ s, c < f i := by
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ i ∈ s, f i ≤ ∑ _i ∈ s, c := Finset.sum_le_sum hcon
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have : c * (s.card : ℝ) = (s.card : ℝ) * c := by ring
  linarith [this ▸ havg]


/-- Lemma `mfd:lem-common`, `eq:mfd-29`, paper lines 3300-3361, in the form the
proof produces.  `Ez = E^g(z)`, `EwB = Γ_E(w)(B)`, `EuB = Γ_E(u_E)(B)`,
`EvE = E^g(v_E)`, `Sg = ‖g‖_∞`, `Mc` is the upper endpoint `M` and `Del` the
gap `Δ`.  `hEuler` is `eq:mfd-28` tested with `φ = z` after Cauchy--Schwarz
(paper lines 3336-3344) and `hEvE_le` is `eq:mfd-14` for `v_E`. -/
theorem common_potential_change_energy_bound
    (Cz m Mc Del Sg Ez EwB EuB EvE : ℝ) (hm : 0 < m) (hDel : 0 ≤ Del)
    (hSg : 0 ≤ Sg) (hEz : 0 ≤ Ez) (hEwB : 0 ≤ EwB) (hEuB : 0 ≤ EuB)
    (hEvE : 0 ≤ EvE) (hCz : 1 ≤ Cz) (hMc : 0 ≤ Mc)
    (hEuler : m * Ez ≤
      (Sg * Real.exp Sg * Mc * Real.sqrt EwB
        + Sg * Real.exp Sg * Del * Real.sqrt EuB
        + Del * Real.sqrt EvE) * Real.sqrt Ez)
    (hEvE_le : EvE ≤ Cz * Sg ^ 2 * Real.exp (Cz * Sg) * EuB) :
    Ez ≤ 3 * (Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2 * EwB +
      (Sg ^ 2 * Real.exp (2 * Sg) + Cz * Sg ^ 2 * Real.exp (Cz * Sg)) *
        Del ^ 2 * EuB) / m ^ 2 := by
  have hA1 : 0 ≤ Sg * Real.exp Sg * Mc * Real.sqrt EwB := by
    have := Real.sqrt_nonneg EwB
    have := (Real.exp_pos Sg).le
    positivity
  have hA2 : 0 ≤ Sg * Real.exp Sg * Del * Real.sqrt EuB := by
    have := Real.sqrt_nonneg EuB
    positivity
  have hA3 : 0 ≤ Del * Real.sqrt EvE := by
    have := Real.sqrt_nonneg EvE
    positivity
  have hmain := weighted_difference_energy_bound m Ez _ _ _ hm hEz hA1 hA2 hA3 hEuler
  have hsw : Real.sqrt EwB ^ 2 = EwB := Real.sq_sqrt hEwB
  have hsu : Real.sqrt EuB ^ 2 = EuB := Real.sq_sqrt hEuB
  have hsv : Real.sqrt EvE ^ 2 = EvE := Real.sq_sqrt hEvE
  have hexp2 : Real.exp Sg ^ 2 = Real.exp (2 * Sg) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hsq1 : (Sg * Real.exp Sg * Mc * Real.sqrt EwB) ^ 2 =
      Sg ^ 2 * Real.exp (2 * Sg) * Mc ^ 2 * EwB := by
    rw [mul_pow, mul_pow, mul_pow, hexp2, hsw]
  have hsq2 : (Sg * Real.exp Sg * Del * Real.sqrt EuB) ^ 2 =
      Sg ^ 2 * Real.exp (2 * Sg) * Del ^ 2 * EuB := by
    rw [mul_pow, mul_pow, mul_pow, hexp2, hsu]
  have hsq3 : (Del * Real.sqrt EvE) ^ 2 = Del ^ 2 * EvE := by
    rw [mul_pow, hsv]
  rw [hsq1, hsq2, hsq3] at hmain
  refine hmain.trans ?_
  rw [div_le_div_iff_of_pos_right (by positivity)]
  have hdel2 : 0 ≤ Del ^ 2 := sq_nonneg Del
  nlinarith [hEvE_le, hdel2]

/-- Lemma `mfd:lem-relvar`, `eq:mfd-30`, paper lines 3362-3399: the five
displayed contributions sum to a bound of the form
`C‖g‖e^{C‖g‖}[Δν(B) + √(ν(B)ζ(B))]`. -/
theorem relative_variation_bound
    (Sg Del Mc Cc nuB zeB T1 T2 T3 T4 T5 : ℝ)
    (hSg : 0 ≤ Sg) (hDel : 0 ≤ Del) (hMc : 1 ≤ Mc) (hCc : 1 ≤ Cc)
    (hnu : 0 ≤ nuB) (hze : 0 ≤ zeB)
    (h1 : |T1| ≤ Sg * Real.exp Sg * Del * nuB)
    (h2 : |T2| ≤ Sg * Real.exp Sg * (2 * Mc) * Real.sqrt (nuB * zeB))
    (h3 : |T3| ≤ Sg * Real.exp Sg * (Cc * Mc) * Real.sqrt (nuB * zeB))
    (h4 : |T4| ≤ Cc * Sg ^ 2 * Real.exp (Cc * Sg) *
      (Del * nuB + 2 * Real.sqrt (nuB * zeB)))
    (h5 : |T5| ≤ Cc * Sg * Real.exp (Cc * Sg) * Del * nuB) :
    |T1 + T2 + T3 + T4 + T5| ≤
      (Sg * Real.exp Sg + Cc * Sg ^ 2 * Real.exp (Cc * Sg) +
          Cc * Sg * Real.exp (Cc * Sg)) * (Del * nuB) +
        (Sg * Real.exp Sg * (2 * Mc + Cc * Mc) +
          2 * Cc * Sg ^ 2 * Real.exp (Cc * Sg)) * Real.sqrt (nuB * zeB) := by
  have habs : |T1 + T2 + T3 + T4 + T5| ≤ |T1| + |T2| + |T3| + |T4| + |T5| := by
    have b1 := abs_add_le (T1 + T2 + T3 + T4) T5
    have b2 := abs_add_le (T1 + T2 + T3) T4
    have b3 := abs_add_le (T1 + T2) T3
    have b4 := abs_add_le T1 T2
    linarith
  linarith [habs, h1, h2, h3, h4, h5]

/-- Lemma `mfd:lem-mass`, paper lines 3627-3655: with the four losses at most
`1/8` in total, the average of the good padded doubling mass over the selected
levels and shifts exceeds `λ(Q)/4`, so some level and shift realizes it. -/
theorem improving_cells_carry_mass {ι : Type*} (s : Finset ι) (good : ι → ℝ)
    (lamQ losses : ℝ) (hlam : 0 < lamQ) (hloss : losses ≤ 1 / 8)
    (hcard : 0 < s.card)
    (havg : (1 / 2 - losses) * lamQ * (s.card : ℝ) ≤ ∑ i ∈ s, good i) :
    ∃ i ∈ s, lamQ / 4 < good i := by
  refine exists_index_gt_of_average_gt s good (lamQ / 4) ?_
  have hc : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hcard
  have hlt : lamQ / 4 * (s.card : ℝ) < (1 / 2 - losses) * lamQ * (s.card : ℝ) := by
    apply mul_lt_mul_of_pos_right _ hc
    nlinarith
  linarith

end Lane3
end SubdiffusiveProcess
