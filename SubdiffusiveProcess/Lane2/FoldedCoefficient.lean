import SubdiffusiveProcess.Lane2.BoxReflection
import SubdiffusiveProcess.Geometry.CoordinateFold

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology Distributions ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}




theorem lane2_coordinateFold_apply_of_notMem {z : SpatialCoordinates d}
    {I : Finset (Fin d)} {j : Fin d} (hj : j ∉ I) (y : SpatialCoordinates d) :
    coordinateFold z I I y j = y j := by
  simp [coordinateFold, hj]

theorem lane2_coordinateFold_apply_of_le {z : SpatialCoordinates d}
    {I : Finset (Fin d)} {j : Fin d} (hj : j ∈ I) {y : SpatialCoordinates d}
    (h : y j ≤ z j) : coordinateFold z I I y j = y j := by
  simp only [coordinateFold, if_pos hj, coordinateReflectionSign, if_pos hj,
    abs_of_nonpos (sub_nonpos.mpr h)]
  ring

theorem lane2_coordinateFold_apply_of_ge {z : SpatialCoordinates d}
    {I : Finset (Fin d)} {j : Fin d} (hj : j ∈ I) {y : SpatialCoordinates d}
    (h : z j ≤ y j) : coordinateFold z I I y j = 2 * z j - y j := by
  simp only [coordinateFold, if_pos hj, coordinateReflectionSign, if_pos hj,
    abs_of_nonneg (sub_nonneg.mpr h)]
  ring

/-- The fold is the identity on the side at or below every active plane. -/
theorem lane2_coordinateFold_eq_self {z : SpatialCoordinates d}
    {I : Finset (Fin d)} {y : SpatialCoordinates d} (h : ∀ j ∈ I, y j ≤ z j) :
    coordinateFold z I I y = y := by
  funext j
  by_cases hj : j ∈ I
  · exact lane2_coordinateFold_apply_of_le hj (h j hj)
  · exact lane2_coordinateFold_apply_of_notMem hj y

/-- The fold agrees with the coordinate reflection on the side at or above every
active plane, so the folded coefficient IS the evenly reflected coefficient. -/
theorem lane2_coordinateFold_eq_reflection {z : SpatialCoordinates d}
    {I : Finset (Fin d)} {y : SpatialCoordinates d} (h : ∀ j ∈ I, z j ≤ y j) :
    coordinateFold z I I y = coordinateReflection z I y := by
  funext j
  by_cases hj : j ∈ I
  · rw [lane2_coordinateFold_apply_of_ge hj (h j hj)]
    simp [coordinateReflection, hj]
  · rw [lane2_coordinateFold_apply_of_notMem hj y]
    simp [coordinateReflection, hj]

/-- A point on every active plane is fixed by the fold. -/
theorem lane2_coordinateFold_fix {z : SpatialCoordinates d} {I : Finset (Fin d)}
    {y : SpatialCoordinates d} (h : ∀ j ∈ I, y j = z j) :
    coordinateFold z I I y = y :=
  lane2_coordinateFold_eq_self fun j hj => le_of_eq (h j hj)

/-- **Adapter A, the coefficient.**  The evenly reflected coefficient as a
POINTWISE function: `a` folded back into the original piece.  `a` is the
fixed-cutoff coefficient `A_N`; no bound uniform in `N` is used. -/
def foldedCoefficient (a : SpatialCoordinates d → ℝ) (z : SpatialCoordinates d)
    (I : Finset (Fin d)) : SpatialCoordinates d → ℝ :=
  fun y => a (coordinateFold z I I y)

theorem continuous_foldedCoefficient {a : SpatialCoordinates d → ℝ} (ha : Continuous a)
    (z : SpatialCoordinates d) (I : Finset (Fin d)) :
    Continuous (foldedCoefficient a z I) :=
  ha.comp (coordinateFold_continuous z I I)

theorem foldedCoefficient_eq_self {a : SpatialCoordinates d → ℝ}
    {z : SpatialCoordinates d} {I : Finset (Fin d)} {y : SpatialCoordinates d}
    (h : ∀ j ∈ I, y j ≤ z j) : foldedCoefficient a z I y = a y := by
  rw [foldedCoefficient, lane2_coordinateFold_eq_self h]

theorem foldedCoefficient_eq_reflection {a : SpatialCoordinates d → ℝ}
    {z : SpatialCoordinates d} {I : Finset (Fin d)} {y : SpatialCoordinates d}
    (h : ∀ j ∈ I, z j ≤ y j) :
    foldedCoefficient a z I y = a (coordinateReflection z I y) := by
  rw [foldedCoefficient, lane2_coordinateFold_eq_reflection h]

theorem foldedCoefficient_pos {a : SpatialCoordinates d → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hbound : ∀ x, lam ≤ a x) (z : SpatialCoordinates d) (I : Finset (Fin d))
    (y : SpatialCoordinates d) : 0 < foldedCoefficient a z I y :=
  lt_of_lt_of_le hlam (hbound _)

/-- **Adapter A, the small-contrast bound.**  At a point `z` lying on every active
plane, continuity and positivity of the fixed-cutoff coefficient make the
normalized oscillation of the folded coefficient at most `delta` on a
sufficiently small ball.  This is the paper's
"continuity and positivity of `A_N` make its normalized oscillation small on a
sufficiently small ball" (`eq:mfd-18`),
at the fixed cutoff `N`: only `Continuous a` and `0 < a z` are used, and no
constant uniform in `N` is produced. -/
theorem exists_ball_foldedCoefficient_smallContrast
    {a : SpatialCoordinates d → ℝ} (ha : Continuous a)
    (z : SpatialCoordinates d) (I : Finset (Fin d)) (hz : 0 < a z)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ y ∈ Metric.ball z rho,
        |(a z)⁻¹ * foldedCoefficient a z I y - 1| ≤ delta := by
  have hcont : Continuous (fun y => (a z)⁻¹ * foldedCoefficient a z I y - 1) :=
    (continuous_const.mul (continuous_foldedCoefficient ha z I)).sub continuous_const
  have hval : (a z)⁻¹ * foldedCoefficient a z I z - 1 = 0 := by
    rw [foldedCoefficient, lane2_coordinateFold_fix (fun j _ => rfl),
      inv_mul_cancel₀ (ne_of_gt hz), sub_self]
  have hne : ContinuousAt (fun y => (a z)⁻¹ * foldedCoefficient a z I y - 1) z :=
    hcont.continuousAt
  have hev : ∀ᶠ y in nhds z,
      |(a z)⁻¹ * foldedCoefficient a z I y - 1| ≤ delta := by
    have h0 : Filter.Tendsto (fun y => (a z)⁻¹ * foldedCoefficient a z I y - 1)
        (nhds z) (nhds 0) := by
      have := hne.tendsto
      rwa [hval] at this
    have := h0 (Metric.closedBall_mem_nhds (0 : ℝ) hdelta)
    filter_upwards [this] with y hy
    simpa [Real.dist_eq, abs_sub_comm] using hy
  obtain ⟨rho, hrho, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  exact ⟨rho, hrho, hball⟩

/-- The folded coefficient inherits the POSITIVE LOWER BOUND of the original,
not merely pointwise positivity: the fold only moves the evaluation point. -/
theorem foldedCoefficient_ge {a : SpatialCoordinates d → ℝ} {lam : ℝ}
    (hbound : ∀ x : SpatialCoordinates d, lam ≤ a x)
    (z : SpatialCoordinates d) (I : Finset (Fin d)) (y : SpatialCoordinates d) :
    lam ≤ foldedCoefficient a z I y :=
  hbound _

end SubdiffusiveProcess
