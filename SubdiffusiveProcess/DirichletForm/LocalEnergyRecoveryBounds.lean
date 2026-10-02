import SubdiffusiveProcess.Sobolev.HarmonicWindowNorms

/-!# Local oscillation bounds from energy measure recovery

Cutoff integrals compare the energy measure of a smaller set with the mass of
its parent. A finite oscillation estimate therefore passes through convergence
of one supported cutoff integral. This module establishes that scalar passage;
it does not claim convergence of energy measures on arbitrary sets.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section
namespace SubdiffusiveProcess

/-- A cutoff equal to one on a set and zero outside a larger set bounds the two masses. -/
theorem integral_cutoff_bounds
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    (B P : Set X) (hB : MeasurableSet B) (hP : MeasurableSet P)
    (chi : X → ℝ) (hchi : Integrable chi mu)
    (hchi0 : ∀ x, 0 ≤ chi x) (hchi1 : ∀ x, chi x ≤ 1)
    (hchiB : ∀ x ∈ B, chi x = 1) (hchiP : ∀ x ∉ P, chi x = 0) :
    (mu B).toReal ≤ ∫ x, chi x ∂mu ∧
      (∫ x, chi x ∂mu) ≤ (mu P).toReal := by
  have hconst : Integrable (fun _ : X => (1 : ℝ)) mu := integrable_const (1 : ℝ)
  have hBint : Integrable (B.indicator (fun _ : X => (1 : ℝ))) mu := hconst.indicator hB
  have hPint : Integrable (P.indicator (fun _ : X => (1 : ℝ))) mu := hconst.indicator hP
  have hBchi : ∀ᵐ x ∂mu, B.indicator (fun _ : X => (1 : ℝ)) x ≤ chi x := by
    filter_upwards with x
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx]
      rw [hchiB x hx]
    · simp only [Set.indicator_of_notMem hx]
      exact hchi0 x
  have hchiP' : ∀ᵐ x ∂mu, chi x ≤ P.indicator (fun _ : X => (1 : ℝ)) x := by
    filter_upwards with x
    by_cases hx : x ∈ P
    · simp only [Set.indicator_of_mem hx]
      exact hchi1 x
    · simp only [Set.indicator_of_notMem hx]
      rw [hchiP x hx]
  have hconstB : (∫ x in B, (1 : ℝ) ∂mu) = (mu B).toReal := by
    rw [integral_const]
    simp only [smul_eq_mul, mul_one]
    change ENNReal.toReal ((mu.restrict B) Set.univ) = ENNReal.toReal (mu B)
    rw [Measure.restrict_apply_univ]
  have hconstP : (∫ x in P, (1 : ℝ) ∂mu) = (mu P).toReal := by
    rw [integral_const]
    simp only [smul_eq_mul, mul_one]
    change ENNReal.toReal ((mu.restrict P) Set.univ) = ENNReal.toReal (mu P)
    rw [Measure.restrict_apply_univ]
  constructor
  · calc
      (mu B).toReal = ∫ x in B, (1 : ℝ) ∂mu := hconstB.symm
      _ = ∫ x, B.indicator (fun _ : X => (1 : ℝ)) x ∂mu := (integral_indicator hB).symm
      _ ≤ ∫ x, chi x ∂mu := integral_mono_ae hBint hchi hBchi
  · calc
      (∫ x, chi x ∂mu) ≤ ∫ x, P.indicator (fun _ : X => (1 : ℝ)) x ∂mu :=
        integral_mono_ae hchi hPint hchiP'
      _ = ∫ x in P, (1 : ℝ) ∂mu := integral_indicator hP
      _ = (mu P).toReal := hconstP

/-- A finite local oscillation estimate passes to the parent mass of the limiting energy measure. -/
theorem oscillation_bound_of_energy_measure_recovery
    {X : Type*} [MeasurableSpace X]
    (muN : ℕ → Measure X) (mu : Measure X)
    [hfinN : ∀ n, IsFiniteMeasure (muN n)] [IsFiniteMeasure mu]
    (B P : Set X) (hB : MeasurableSet B) (hP : MeasurableSet P)
    (chi : X → ℝ) (hchiN : ∀ n, Integrable chi (muN n))
    (hchi : Integrable chi mu)
    (hchi0 : ∀ x, 0 ≤ chi x) (hchi1 : ∀ x, chi x ≤ 1)
    (hchiB : ∀ x ∈ B, chi x = 1) (hchiP : ∀ x ∉ P, chi x = 0)
    (hrec : Tendsto (fun n => ∫ x, chi x ∂muN n) atTop (𝓝 (∫ x, chi x ∂mu)))
    (aN : ℕ → ℝ) (a : ℝ) (haN : ∀ n, 0 < aN n) (ha : 0 < a)
    (halim : Tendsto aN atTop (𝓝 a))
    (oscN : ℕ → ℝ) (osc : ℝ) (hosc : Tendsto oscN atTop (𝓝 osc))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, oscN n ^ 2 ≤ C * (aN n)⁻¹ * (muN n B).toReal) :
    osc ^ 2 ≤ C * a⁻¹ * (mu P).toReal := by
  have hcutN : ∀ n, (muN n B).toReal ≤ ∫ x, chi x ∂muN n ∧
      (∫ x, chi x ∂muN n) ≤ (muN n P).toReal := by
    intro n
    exact integral_cutoff_bounds (muN n) B P hB hP chi (hchiN n)
      hchi0 hchi1 hchiB hchiP
  have hfactorN : ∀ n, 0 ≤ C * (aN n)⁻¹ := by
    intro n
    exact mul_nonneg hC (inv_nonneg.mpr (le_of_lt (haN n)))
  have hboundCut : ∀ n,
      oscN n ^ 2 ≤ C * (aN n)⁻¹ * (∫ x, chi x ∂muN n) := by
    intro n
    exact (hbound n).trans (mul_le_mul_of_nonneg_left (hcutN n).1 (hfactorN n))
  have hcutlim : Tendsto
      (fun n => C * (aN n)⁻¹ * (∫ x, chi x ∂muN n)) atTop
      (𝓝 (C * a⁻¹ * (∫ x, chi x ∂mu))) := by
    exact (tendsto_const_nhds.mul (halim.inv₀ (ne_of_gt ha))).mul hrec
  have hlimit : osc ^ 2 ≤ C * a⁻¹ * (∫ x, chi x ∂mu) :=
    le_of_tendsto_of_tendsto (hosc.pow 2) hcutlim (Filter.Eventually.of_forall hboundCut)
  exact hlimit.trans (mul_le_mul_of_nonneg_left
    (integral_cutoff_bounds mu B P hB hP chi hchi hchi0 hchi1 hchiB hchiP).2
    (mul_nonneg hC (inv_nonneg.mpr ha.le)))

end SubdiffusiveProcess
