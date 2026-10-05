module

public import Mathlib

@[expose] public section

open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- A retained-cell union sum is finite when its cell count and one-cell
tail are bounded by geometric sequences whose product has base below one. -/
theorem aux_shallow_envelope_numeric_tsum
    {α : Type*} (G : ℕ → Finset α)
    (A : ℕ → ℝ≥0∞) (Cg Cb r u : ℝ≥0∞)
    (hCg : Cg < ∞) (hCb : Cb < ∞) (hru : r * u < 1)
    (hcard : ∀ k, (G k).card ≤ Cg * r ^ k)
    (hcell : ∀ k, A k ≤ Cb * u ^ k)
    : (∑' k : ℕ, (G k).card * A k) ≠ ∞ := by
  have hgeom : (∑' k : ℕ, (Cg * Cb) * (r * u) ^ k) ≠ ∞ := by
    have hsum' : (∑' k : ℕ, (Cg * Cb) * (r * u) ^ k) = (Cg * Cb) * (1 - r * u)⁻¹ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    rw [hsum']
    have hden : (1 - r * u)⁻¹ < ∞ := by
      simpa only [ENNReal.tsum_geometric] using (tsum_geometric_lt_top.mpr hru)
    have hconst : Cg * Cb < ∞ := ENNReal.mul_lt_top hCg hCb
    exact ENNReal.mul_lt_top hconst hden |>.ne
  have hle : ∀ k, (G k).card * A k ≤ (Cg * Cb) * (r * u) ^ k := by
    intro k
    calc
      (G k).card * A k ≤ (Cg * r ^ k) * (Cb * u ^ k) :=
        mul_le_mul (hcard k) (hcell k) zero_le zero_le
      _ = (Cg * Cb) * (r * u) ^ k := by rw [mul_pow]; ring_nf
  exact ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum hle)

/-- The source rate calculation for exponentially growing moments and
thresholds. The strict inequality `d < p (rho - eta)` makes the cell count
times the Markov tail a summable geometric sequence. -/
theorem lem_as_coarse_shallow_grid_envelope_rate
    {α : Type*} (G : ℕ → Finset α)
    (d p B0 Cg eta rho : ℝ)
    (hp : 0 < p) (hB0 : 0 ≤ B0) (hCg : 0 ≤ Cg)
    (heta : eta < rho) (hrate : d < p * (rho - eta))
    (hcard : ∀ k : ℕ,
      ((G k).card : ℝ) ≤ Cg * (3 : ℝ) ^ (d * (k : ℝ))) :
    (∑' k : ℕ, (G k).card *
      (ENNReal.ofReal
        ((B0 * (3 : ℝ) ^ (eta * (k : ℝ))) /
          (3 : ℝ) ^ (rho * (k : ℝ))) ^ p)) ≠ ∞ := by
  let r : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ d)
  let u : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ (-p * (rho - eta)))
  let Cb : ℝ≥0∞ := ENNReal.ofReal (B0 ^ p)
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h31 : (1 : ℝ) < 3 := by norm_num
  have hdelta : 0 < rho - eta := by linarith
  have hslack : d - p * (rho - eta) < 0 := by linarith
  have hru : r * u < 1 := by
    rw [show r * u = ENNReal.ofReal ((3 : ℝ) ^ d * (3 : ℝ) ^ (-p * (rho - eta))) by
      dsimp [r, u]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) d)]]
    have hexp : (3 : ℝ) ^ d * (3 : ℝ) ^ (-p * (rho - eta)) =
        (3 : ℝ) ^ (d - p * (rho - eta)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring_nf
    rw [hexp, ENNReal.ofReal_lt_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg h31 hslack
  have hcell : ∀ k : ℕ,
      ENNReal.ofReal
        ((B0 * (3 : ℝ) ^ (eta * (k : ℝ))) /
          (3 : ℝ) ^ (rho * (k : ℝ))) ^ p ≤ Cb * u ^ k := by
    intro k
    have hpowpos : 0 ≤ (3 : ℝ) ^ ((eta - rho) * (k : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hratio :
        (B0 * (3 : ℝ) ^ (eta * (k : ℝ))) /
          (3 : ℝ) ^ (rho * (k : ℝ)) =
        B0 * (3 : ℝ) ^ ((eta - rho) * (k : ℝ)) := by
      calc
        _ = B0 * ((3 : ℝ) ^ (eta * (k : ℝ)) /
            (3 : ℝ) ^ (rho * (k : ℝ))) := by ring
        _ = B0 * (3 : ℝ) ^ ((eta - rho) * (k : ℝ)) := by
          congr 1
          rw [← Real.rpow_sub h3]
          congr 1
          ring_nf
    have hpower :
        (B0 * (3 : ℝ) ^ ((eta - rho) * (k : ℝ))) ^ p =
          B0 ^ p * (3 : ℝ) ^ ((-p * (rho - eta)) * (k : ℝ)) := by
      rw [Real.mul_rpow hB0 hpowpos]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
        ((eta - rho) * (k : ℝ)) p]
      congr 1
      ring_nf
    have hleft_nonneg :
        0 ≤ (B0 * (3 : ℝ) ^ ((eta - rho) * (k : ℝ))) :=
      mul_nonneg hB0 hpowpos
    have hright_nonneg : 0 ≤ B0 ^ p := Real.rpow_nonneg hB0 _
    have hpowtoNat :
        (3 : ℝ) ^ ((-p * (rho - eta)) * (k : ℝ)) =
          ((3 : ℝ) ^ (-p * (rho - eta))) ^ k := by
      rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    have hEq : ENNReal.ofReal
        ((B0 * (3 : ℝ) ^ (eta * (k : ℝ))) /
          (3 : ℝ) ^ (rho * (k : ℝ))) ^ p = Cb * u ^ k := by
      calc
        ENNReal.ofReal
            ((B0 * (3 : ℝ) ^ (eta * (k : ℝ))) /
              (3 : ℝ) ^ (rho * (k : ℝ))) ^ p =
          ENNReal.ofReal (B0 ^ p) *
            ENNReal.ofReal ((3 : ℝ) ^ (-p * (rho - eta))) ^ k := by
              rw [hratio, ENNReal.ofReal_rpow_of_nonneg hleft_nonneg hp.le,
                hpower, ENNReal.ofReal_mul hright_nonneg, hpowtoNat,
                ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _) k]
        _ = Cb * u ^ k := by rfl
    exact hEq.le
  have hcard' : ∀ k : ℕ, (G k).card ≤ ENNReal.ofReal Cg * r ^ k := by
    intro k
    have hpowNat :
        (3 : ℝ) ^ (d * (k : ℝ)) = ((3 : ℝ) ^ d) ^ k :=
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) d k
    have hconstPow : ENNReal.ofReal (Cg * (3 : ℝ) ^ (d * (k : ℝ))) =
        ENNReal.ofReal Cg * r ^ k := by
      rw [ENNReal.ofReal_mul hCg, hpowNat, ENNReal.ofReal_pow
        (Real.rpow_nonneg (by norm_num) d) k]
    rw [← ENNReal.ofReal_natCast]
    calc
      ENNReal.ofReal ((G k).card : ℝ) ≤
          ENNReal.ofReal (Cg * (3 : ℝ) ^ (d * (k : ℝ))) :=
        ENNReal.ofReal_le_ofReal (hcard k)
      _ = ENNReal.ofReal Cg * r ^ k := hconstPow
  have hCgTop : ENNReal.ofReal Cg < ∞ := ENNReal.ofReal_lt_top
  have hCbTop : Cb < ∞ := by
    dsimp [Cb]
    exact ENNReal.ofReal_lt_top
  exact aux_shallow_envelope_numeric_tsum G
    (fun k => ENNReal.ofReal
      ((B0 * (3 : ℝ) ^ (eta * (k : ℝ))) /
        (3 : ℝ) ^ (rho * (k : ℝ))) ^ p)
    (ENNReal.ofReal Cg) Cb r u hCgTop hCbTop (by simpa [r, u] using hru)
    hcard' hcell

end SubdiffusiveProcess.Paper
