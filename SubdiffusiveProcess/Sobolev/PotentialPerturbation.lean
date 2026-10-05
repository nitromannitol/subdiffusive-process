module

public import SubdiffusiveProcess.Sobolev.ResponsePerturbation
public import SubdiffusiveProcess.Sobolev.PotentialCoefficient

@[expose] public section

/-! # Local potential changes on the actual Sobolev responses

The coefficient assumptions for relative perturbation are derived from the
actual exponential identity. The constants depend on the changed potential
only, and the support and original local energy are retained.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- The actual exponential coefficients have all relative bounds on one common ae event. -/
theorem expPotentialCoefficient_add_relative_bounds
    (h g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    {s : Set (SpatialCoordinates d)}
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∉ s → g x = 0) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      Real.exp (-‖g‖) * (expPotentialCoefficient h).val x ≤ (expPotentialCoefficient (h + g)).val x ∧
      |(expPotentialCoefficient (h + g)).val x - (expPotentialCoefficient h).val x| ≤
        (‖g‖ * Real.exp ‖g‖) * (expPotentialCoefficient h).val x ∧
      (expPotentialCoefficient (h + g)).val x ≤ Real.exp ‖g‖ * (expPotentialCoefficient h).val x ∧
      (x ∉ s → (expPotentialCoefficient (h + g)).val x = (expPotentialCoefficient h).val x) := by
  filter_upwards [expPotentialCoefficient_coeFn h, expPotentialCoefficient_coeFn (h + g),
    Lp.coeFn_add h g, boundedPotential_ae_bound g, hsupp] with x hh hhg hadd hbound hzero
  have he : (expPotentialCoefficient (h + g)).val x = Real.exp (g x) * (expPotentialCoefficient h).val x := by
    rw [hhg, hadd, Pi.add_apply, Real.exp_add, hh, mul_comm]
  have ha : 0 < (expPotentialCoefficient h).val x := by rw [hh]; exact Real.exp_pos _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    exact mul_le_mul_of_nonneg_right (Real.exp_monotone (abs_le.mp hbound).1) ha.le
  · calc
      _ = |Real.exp (g x) - 1| * (expPotentialCoefficient h).val x := by
        rw [he, ← sub_one_mul, abs_mul, abs_of_pos ha]
      _ ≤ _ := mul_le_mul_of_nonneg_right (abs_exp_sub_one_le_bound hbound) ha.le
  · rw [he]
    exact mul_le_mul_of_nonneg_right (Real.exp_monotone (abs_le.mp hbound).2) ha.le
  · intro hx
    rw [he, hzero hx, Real.exp_zero, one_mul]

/-- Local potential stability for canonical source solutions and inverse responses. -/
theorem source_responses_potential_stability (S : ResponseSpace Ω)
    (h g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∉ s → g x = 0)
    (L : S.space →L[ℝ] ℝ) :
    let a := expPotentialCoefficient h
    let b := expPotentialCoefficient (h + g)
    let u := responseSolution S a L
    let v := responseSolution S b L
    let m := localGradientEnergy a hs (subspaceGradient S.space u)
    let δ := ‖g‖ * Real.exp ‖g‖
    let c := Real.exp (-‖g‖)
    responseForm S b (v - u) (v - u) ≤ δ ^ 2 / c * m ∧
      localGradientEnergy b hs (subspaceGradient S.space v) ≤
        2 * Real.exp ‖g‖ * (1 + δ ^ 2 / c ^ 2) * m ∧
      |inverseResponse S b L - inverseResponse S a L| ≤ (δ + δ ^ 2 / c) * m := by
  have hb := expPotentialCoefficient_add_relative_bounds h g hsupp
  exact source_responses_localized_stability S _ _ hs (Real.exp_pos _) (Real.exp_nonneg _)
    (hb.mono fun _ hx => hx.1) (hb.mono fun _ hx => hx.2.1)
    (hb.mono fun _ hx => hx.2.2.1) (hb.mono fun _ hx => hx.2.2.2) L

/-- The same local potential estimates hold jointly for the actual boundary minimum. -/
theorem boundary_responses_potential_stability (S : ResponseSpace Ω)
    (h g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∉ s → g x = 0)
    (f : weakSobolevGraph Ω) :
    let a := expPotentialCoefficient h
    let b := expPotentialCoefficient (h + g)
    let u := dirichletMinimizer S a f
    let v := dirichletMinimizer S b f
    let m := localGradientEnergy a hs (sobolevGradient u.val)
    let δ := ‖g‖ * Real.exp ‖g‖
    let c := Real.exp (-‖g‖)
    sobolevCoefficientForm b (v.val - u.val) (v.val - u.val) ≤ δ ^ 2 / c * m ∧
      localGradientEnergy b hs (sobolevGradient v.val) ≤
        2 * Real.exp ‖g‖ * (1 + δ ^ 2 / c ^ 2) * m ∧
      |dirichletResponse S b f - dirichletResponse S a f| ≤ (δ + δ ^ 2 / c) * m := by
  have hb := expPotentialCoefficient_add_relative_bounds h g hsupp
  exact boundary_responses_localized_stability S _ _ hs (Real.exp_pos _) (Real.exp_nonneg _)
    (hb.mono fun _ hx => hx.1) (hb.mono fun _ hx => hx.2.1)
    (hb.mono fun _ hx => hx.2.2.1) (hb.mono fun _ hx => hx.2.2.2) f

end SubdiffusiveProcess
