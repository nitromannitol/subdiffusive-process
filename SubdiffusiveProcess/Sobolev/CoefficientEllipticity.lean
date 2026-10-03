module

public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.GradientRange

@[expose] public section

/-!
# A pointwise ellipticity lower bound for `sobolevCoefficientForm`

`sobolevCoefficientForm_mono` (`Sobolev/DirichletComparison.lean`) compares two coefficients;
this file specializes the same underlying `weightedGradientForm`/`weightedL2Form` ellipticity
estimate (already used internally by `sobolevCoefficientForm_nonneg`) to a single explicit
uniform lower bound `c`, giving the energy a genuine coercive estimate in terms of the plain
(unweighted) gradient Hilbert norm `‖sobolevGradient u‖`.
-/

open MeasureTheory Set TopologicalSpace
namespace SubdiffusiveProcess

/-- A uniform pointwise lower bound `c ≤ a` on the coefficient bounds the weighted energy below
by `c` times the squared (unweighted) gradient norm. -/
theorem sobolevCoefficientForm_ellipticity_lower {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {c : ℝ}
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      c ≤ (a.val : SpatialCoordinates d → ℝ) x)
    (u : SobolevData Ω) :
    c * ‖sobolevGradient u‖ ^ 2 ≤ sobolevCoefficientForm a u u := by
  have hg : c * ‖sobolevGradient u‖ * ‖sobolevGradient u‖ ≤
      weightedGradientForm a.val (sobolevGradient u) (sobolevGradient u) := by
    calc c * ‖sobolevGradient u‖ * ‖sobolevGradient u‖
        = ∑ i : Fin d, c * ‖(sobolevGradient u) i‖ ^ 2 := by
          rw [mul_assoc, ← pow_two, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      _ ≤ ∑ i : Fin d, weightedL2Form a.val ((sobolevGradient u) i) ((sobolevGradient u) i) :=
          Finset.sum_le_sum fun i _ => weightedL2Form_lower a.val ha _
      _ = weightedGradientForm a.val (sobolevGradient u) (sobolevGradient u) := by
          simp only [weightedGradientForm, ContinuousLinearMap.sum_apply,
            ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply]
  calc c * ‖sobolevGradient u‖ ^ 2 = c * ‖sobolevGradient u‖ * ‖sobolevGradient u‖ := by ring
    _ ≤ weightedGradientForm a.val (sobolevGradient u) (sobolevGradient u) := hg
    _ = sobolevCoefficientForm a u u := rfl

end SubdiffusiveProcess
