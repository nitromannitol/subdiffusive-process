import SubdiffusiveProcess.Paper.prop_conc_masked_core_mass
import SubdiffusiveProcess.DirichletForm.LocalEnergyQuadratic

/-! A finite affine slope family has local energy growth controlled by the coordinate family.
The comparison is deterministic and uses the same positive response denominator on both sides. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- Coordinate energy measures control the normalized measure of every fixed finite slope family. -/
theorem prop_conc_slope_measure_bound
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X} {d : ℕ}
    (E : DirichletForm.ClosedForm mu) (Gamma : DirichletForm.EnergyMeasure E)
    (u v : (Fin d → ℝ) →ₗ[ℝ] Lp ℝ 2 mu)
    (hu : ∀ p, u p ∈ E.domain) (hv : ∀ p, v p ∈ E.domain)
    (slopes : Finset (Fin d → ℝ)) (D : ℝ) (hD : 0 < D)
    (A : Set X) (hA : MeasurableSet A) :
    ((ENNReal.ofReal D⁻¹ • ∑ p ∈ slopes, (Gamma.measure (u p) + Gamma.measure (v p))) A).toReal ≤
      ((2 : ℝ) ^ d * ∑ p ∈ slopes, ∑ i : Fin d, (p i) ^ 2) *
        ((ENNReal.ofReal D⁻¹ • ∑ i : Fin d,
          (Gamma.measure (u (Pi.single i 1)) + Gamma.measure (v (Pi.single i 1)))) A).toReal := by
  let Q : QuadraticForm ℝ (Fin d → ℝ) := Gamma.localQuadratic u hu A + Gamma.localQuadratic v hv A
  have hQ (p : Fin d → ℝ) : Q p = (Gamma.measure (u p) A).toReal + (Gamma.measure (v p) A).toReal := by
    exact congrArg₂ (· + ·) (Gamma.localQuadratic_apply u hu A hA p)
      (Gamma.localQuadratic_apply v hv A hA p)
  have hQ0 (p : Fin d → ℝ) : 0 ≤ Q p := by rw [hQ]; positivity
  have hsum : (∑ p ∈ slopes, Q p) ≤
      ((2 : ℝ) ^ d * ∑ p ∈ slopes, ∑ i : Fin d, (p i) ^ 2) *
        ∑ i : Fin d, Q (Pi.single i 1) := by
    calc
      _ ≤ ∑ p ∈ slopes, ((2 : ℝ) ^ d * (∑ i : Fin d, (p i) ^ 2) * ∑ i : Fin d, Q (Pi.single i 1)) :=
        Finset.sum_le_sum fun p _ => aux_relative_response_variation_quad_bound d Q hQ0 _ rfl p
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [aux_prop_conc_masked_core_mass_normalized_pair_mass Gamma u v hu hv slopes D hD A,
    aux_prop_conc_masked_core_mass_normalized_pair_mass Gamma (fun i : Fin d => u (Pi.single i 1))
      (fun i : Fin d => v (Pi.single i 1)) (fun i => hu _) (fun i => hv _) Finset.univ D hD A]
  simp_rw [hQ] at hsum
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hD.le)
  convert h using 1 <;> ring

end
end Paper
