module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Sobolev.HarmonicTraceLimit

@[expose] public section

/-!+# Scalar norms in the harmonic comparison limit

Bounded sources control their volume-normalized finite-exponent norms, and
uniform convergence preserves centered L2 oscillations. This file does not
assert a PDE estimate or a stochastic bound.
-/

open Filter MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal

namespace SubdiffusiveProcess

/-- A pointwise bound controls the finite-exponent Lp norm after volume normalization. -/
private theorem raw_eLpNorm_le_of_ae_bound
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (p : ℝ) (hp : 0 < p) (f : X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂mu, |f x| ≤ C) :
    SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal p) mu ≤
      mu Set.univ ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal C := by
  calc
    SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal p) mu ≤
        SubdiffusiveProcess.RawLp.eLpNorm (fun _ : X => C) (ENNReal.ofReal p) mu :=
      SubdiffusiveProcess.RawLp.eLpNorm_mono_ae (hf.mono fun x hx => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using! hx)
    _ = mu Set.univ ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal C := by
      rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded aestronglyMeasurable_const,
        MeasureTheory.eLpNorm_const' C (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top,
        Real.enorm_eq_ofReal_abs, abs_of_nonneg hC]
      simp only [one_div, mul_comm]

theorem normalized_eLpNorm_le_of_ae_bound
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (p : ℝ) (hp : 0 < p) (f : X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂mu, |f x| ≤ C) :
    (SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal p) mu).toReal /
      (mu Set.univ).toReal ^ (1 / p) ≤ C := by
  have hbound := raw_eLpNorm_le_of_ae_bound mu p hp f C hC hf
  have hfinite : mu Set.univ ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg
      (inv_nonneg.mpr ENNReal.toReal_nonneg) (measure_ne_top mu Set.univ)) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfinite hbound
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hC] at hreal
  by_cases hz : (mu Set.univ).toReal = 0
  · rw [hz, Real.zero_rpow (one_div_pos.mpr hp).ne', div_zero]
    exact hC
  · have hpos : 0 < (mu Set.univ).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hpos (1 / p))).mpr
    simpa only [one_div, mul_comm] using! hreal

/-- Uniform convergence preserves the normalized centered L2 oscillation. -/
theorem tendsto_centered_normalizedL2_of_tendstoUniformlyOn
    {d : ℕ} (W : Set (SpatialCoordinates d)) (hWm : MeasurableSet W)
    (hWpos : 0 < volume.real W) (hWtop : volume W ≠ ⊤)
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hN : ∀ n, MemLp (UN n) 2 (volume.restrict W))
    (hU : MemLp U 2 (volume.restrict W))
    (hlim : TendstoUniformlyOn UN U atTop W) :
    Tendsto (fun n => normalizedL2On W
      (fun x => UN n x - (volume.real W)⁻¹ * ∫ y in W, UN n y)) atTop
      (𝓝 (normalizedL2On W
        (fun x => U x - (volume.real W)⁻¹ * ∫ y in W, U y))) := by
  let hfinite : IsFiniteMeasure (volume.restrict W) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hWtop.lt_top⟩
  have hsub := Section6TheoremC.tendsto_centeredNormalizedL2On_sub_of_tendsto_sub
    hWm hWpos hWtop hN hU
    (tendsto_normalizedL2_sub_of_tendstoUniformlyOn W hWm hWpos hWtop UN U hN hU hlim)
  exact Section6TheoremC.tendsto_normalizedL2On_of_tendsto_sub
    (fun n => (hN n).sub (memLp_const _)) (hU.sub (memLp_const _)) hsub

end SubdiffusiveProcess
