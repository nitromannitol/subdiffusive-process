import SubdiffusiveProcess.Analysis.ReferenceInverseLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Passing scalar coefficient inverse bounds through convergence in measure.
No coefficient or source estimates are established here. -/
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess

/-- Coefficient order and a pathwise inverse cap bound the reference on the normalized upper-limit event. -/
theorem ae_reference_inv_le_of_coefficient_limits
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lower upper scale : ℕ → Ω → ℝ) (s ell K : Ω → ℝ) (C : ℝ)
    (hpath : ∀ᵐ ω ∂P,
      (∀ n, 0 < lower n ω) ∧ (∀ n, lower n ω ≤ upper n ω) ∧
      (∀ᶠ n in atTop, (lower n ω)⁻¹ ≤ K ω) ∧ 0 ≤ K ω ∧ 0 < s ω ∧
      Tendsto (fun n => scale n ω) atTop (𝓝 (s ω)))
    (hNorm : TendstoInMeasure P (fun n ω => upper n ω / scale n ω) atTop ell) :
    ∀ᵐ ω ∂P, ell ω ≤ C → (s ω)⁻¹ ≤ K ω * C := by
  obtain ⟨rho, hrho, hNormAE⟩ := hNorm.exists_seq_tendsto_ae
  filter_upwards [hpath, hNormAE] with ω hω hn
  intro hell
  exact reference_inv_le_of_coefficient_limits
    (fun n => lower (rho n) ω) (fun n => upper (rho n) ω)
    (fun n => scale (rho n) ω) (s ω) (ell ω) (K ω) C
    (fun n => hω.1 (rho n)) (fun n => hω.2.1 (rho n))
    (hrho.tendsto_atTop.eventually hω.2.2.1) hω.2.2.2.1 hω.2.2.2.2.1 hell
    (hω.2.2.2.2.2.comp hrho.tendsto_atTop) hn

end SubdiffusiveProcess
