import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Paper.lane4_dilation_quasi_measure_preserving

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lane4_gagliardo_dilation_double_integral :
  ∀ (d k : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (s : ℝ), 0 < s →
  ∀ (F G : Fin k → SpatialCoordinates d → ℝ),
    (∀ (i : Fin k) (x : SpatialCoordinates d), G i x = F i (cubeDilation z z' r x)) →
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (F i x - F i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s)) =
      ENNReal.ofReal (r ^ ((d : ℝ) - 2 * s)) *
        ∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
            ENNReal.ofReal (∑ i : Fin k, (G i x - G i y) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * s) := by
  intro d k z z' r hr h1 s hs F G hG
  have hepos : (0:ℝ) < (d : ℝ) + 2 * s := by positivity
  set c : ℝ≥0∞ := (ENNReal.ofReal r) ^ ((d : ℝ) + 2 * s) with hcdef
  have hor : ENNReal.ofReal r ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hr
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact fun h => hor (by
      rcases ENNReal.rpow_eq_zero_iff.1 h with ⟨h', _⟩ | ⟨h', _⟩
      · exact h'
      · exact absurd h' ENNReal.ofReal_ne_top)
  have hctop : c ≠ ⊤ := by
    rw [hcdef]
    exact fun h => by
      rcases ENNReal.rpow_eq_top_iff.1 h with ⟨h', _⟩ | ⟨h', _⟩
      · exact hor h'
      · exact ENNReal.ofReal_ne_top h'
  -- the pointwise kernel identity
  have hkernel : ∀ x0 y0 : SpatialCoordinates d,
      ENNReal.ofReal (∑ i : Fin k,
          (F i (cubeDilation z z' r x0) - F i (cubeDilation z z' r y0)) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
          (cubeDilation z z' r x0 j - cubeDilation z z' r y0 j) ^ 2))) ^ ((d : ℝ) + 2 * s)
      = c⁻¹ * (ENNReal.ofReal (∑ i : Fin k, (G i x0 - G i y0) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2))) ^
            ((d : ℝ) + 2 * s)) := by
    intro x0 y0
    have hnum : (∑ i : Fin k,
        (F i (cubeDilation z z' r x0) - F i (cubeDilation z z' r y0)) ^ 2)
        = ∑ i : Fin k, (G i x0 - G i y0) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hG i x0, hG i y0]
    rw [hnum, sqrt_sum_sq_cubeDilation z z' hr x0 y0, ENNReal.ofReal_mul hr.le,
      ENNReal.mul_rpow_of_nonneg _ _ hepos.le, ← hcdef, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
    ring
  -- outer change of variables
  rw [lintegral_centeredCube_cubeDilation z z' hr h1
    (fun x => ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal (∑ i : Fin k, (F i x - F i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * s))]
  -- inner change of variables, pointwise in the outer variable
  have hstep : ∀ x0 : SpatialCoordinates d,
      (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (F i (cubeDilation z z' r x0) - F i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
            (cubeDilation z z' r x0 j - y j) ^ 2))) ^ ((d : ℝ) + 2 * s))
      = ENNReal.ofReal (r ^ d) * (c⁻¹ *
          ∫⁻ y0 in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
            ENNReal.ofReal (∑ i : Fin k, (G i x0 - G i y0) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2))) ^
                ((d : ℝ) + 2 * s)) := by
    intro x0
    rw [lintegral_centeredCube_cubeDilation z z' hr h1
      (fun y => ENNReal.ofReal (∑ i : Fin k, (F i (cubeDilation z z' r x0) - F i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
          (cubeDilation z z' r x0 j - y j) ^ 2))) ^ ((d : ℝ) + 2 * s))]
    congr 1
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0)]
    exact lintegral_congr fun y0 => hkernel x0 y0
  rw [lintegral_congr hstep, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), ← mul_assoc, ← mul_assoc]
  congr 1
  -- the constants
  have hconst : ENNReal.ofReal (r ^ d) * ENNReal.ofReal (r ^ d) * c⁻¹
      = ENNReal.ofReal (r ^ ((d : ℝ) - 2 * s)) := by
    have hrd : ENNReal.ofReal (r ^ d) = ENNReal.ofReal (r ^ ((d : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    have hcr : c = ENNReal.ofReal (r ^ ((d : ℝ) + 2 * s)) := by
      rw [hcdef, ← ENNReal.ofReal_rpow_of_pos hr]
    rw [hrd, hcr, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.rpow_neg hr.le, ← Real.rpow_add hr, ← Real.rpow_add hr]
    congr 1
    ring
  exact hconst

end Paper
