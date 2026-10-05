module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_ahom_ratio
public import Mathlib.Tactic

@[expose] public section

open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- The two-sided exponential pair is dominated by the shallow-grid
`ahom` ratio's deterministic exponential envelope. -/
theorem lem_as_coarse_shallow_grid_ahom_exp_pair
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (N k : ℕ) (hkN : k ≤ N) (g : ℝ) :
    let a := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
    a * Real.exp g + a⁻¹ * Real.exp (-g) ≤
      Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) *
        (Real.exp g + Real.exp (-g)) := by
  dsimp only
  obtain ⟨_, ha, hai⟩ :=
    lem_as_coarse_shallow_grid_ahom_ratio d M Rm N k hkN
  calc
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * Real.exp g +
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * Real.exp (-g) ≤
      Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) *
          Real.exp g +
        Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) *
          Real.exp (-g) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right ha (Real.exp_pos g).le)
              (mul_le_mul_of_nonneg_right hai (Real.exp_pos (-g)).le)
    _ = Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) *
        (Real.exp g + Real.exp (-g)) := by ring

/-- Remove a scalar infrared factor from a positive/inverse pair. -/
theorem aux_shallow_zero_ir_scaled_pair_le
    (t h : ℝ) (ht : 0 < t) :
    Real.exp (-h) * t + Real.exp h * t⁻¹ ≤
      Real.exp |h| * (t + t⁻¹) := by
  have hneg : Real.exp (-h) ≤ Real.exp |h| :=
    Real.exp_le_exp.mpr (neg_le_abs h)
  have hpos : Real.exp h ≤ Real.exp |h| :=
    Real.exp_le_exp.mpr (le_abs_self h)
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  nlinarith [mul_le_mul_of_nonneg_right hneg ht.le,
    mul_le_mul_of_nonneg_right hpos htinv]

/-- The actual scalar factor without infrared potential is controlled by
the corresponding factor with infrared potential. -/
theorem aux_shallow_zero_ir_pair_le
    (s h : ℝ) (hs : 0 < s) :
    s + s⁻¹ ≤ Real.exp |h| *
      ((Real.exp h * s) + (Real.exp h * s)⁻¹) := by
  have ht : 0 < Real.exp h * s := mul_pos (Real.exp_pos _) hs
  have hleft : Real.exp (-h) * (Real.exp h * s) = s := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hright : Real.exp h * (Real.exp h * s)⁻¹ = s⁻¹ := by
    field_simp [ne_of_gt hs, Real.exp_ne_zero]
  simpa only [hleft, hright] using
    (aux_shallow_zero_ir_scaled_pair_le (Real.exp h * s) h ht)

end SubdiffusiveProcess.Paper



