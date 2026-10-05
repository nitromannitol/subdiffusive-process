module

public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Main.CubeFractionalL2
public import SubdiffusiveProcess.Sobolev.FractionalSubtraction

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

theorem scalar_halfFractional_kernel_lt_top
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder) :
    (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal ((u.val 0 y - u.val 0 x)^2) /
          (ENNReal.ofReal (Real.sqrt (∑ i : Fin d, (y i-x i)^2)))^((d : ℝ)+1)) < ⊤ := by
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let a : ℝ≥0∞ := ENNReal.ofReal (halfFractionalOrder : ℝ) / volume U
  let I : ℝ≥0∞ := ∫⁻ x in U,
      ∫⁻ y in U,
        ENNReal.ofReal ((u.val 0 x - u.val 0 y)^2) /
          (ENNReal.ofReal (Real.sqrt (∑ i : Fin d, (x i-y i)^2)))^((d : ℝ)+1)
  have hvoltop : volume U ≠ ⊤ := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hvolpos : 0 < volume U := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_pos.mpr (pow_pos hr _)
  have ha0 : a ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    exact ⟨(ENNReal.ofReal_pos.mpr halfFractionalOrder.2.1).ne', hvoltop⟩
  have hu : (a * I) ^ (1 / 2 : ℝ) < ⊤ := by
    simpa [a, I, U, μ, cubeFractionalL2Seminorm, halfFractionalOrder,
      Fin.sum_univ_succ] using u.property
  have hprod : a * I < ⊤ := by
    by_contra h
    have heq : a * I = ⊤ := top_unique (le_of_not_gt h)
    exact (ne_of_lt hu) (by rw [heq, ENNReal.top_rpow_of_pos (by norm_num)])
  have hI : I < ⊤ := by
    rcases (ENNReal.mul_lt_top_iff.mp hprod) with h | h | h
    · exact h.2
    · exact (ha0 h).elim
    · simp [h]
  simpa [I, U] using hI

end SubdiffusiveProcess
