module

public import SubdiffusiveProcess.Sobolev.WeakGradient
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.EstimateLimits
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SeminormLimits
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.L2Stability

@[expose] public section

/-! # Centered normalized `L²` oscillation is continuous along `L²` convergence

If `fₙ → f` in `L²(Ω)` and `W ⊆ Ω` has finite positive volume, then the centered normalized
`L²` oscillations of any representatives of `fₙ` on `W` converge to that of `f`.  Nothing is
claimed about pointwise or uniform convergence. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal

noncomputable section
namespace SubdiffusiveProcess

/-- The squared `L²(Ω)` norm is the integral of the square. -/
theorem domainL2_norm_sq_eq_integral {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (G : DomainL2 Ω) :
    ‖G‖ ^ 2 = ∫ x in (Ω : Set (SpatialCoordinates d)), (G x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- `L²(Ω)` convergence gives vanishing normalized `L²` distance on a subwindow. -/
theorem tendsto_normalizedL2On_sub_of_tendsto_domainL2 {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (W : Set (SpatialCoordinates d))
    (hWΩ : W ⊆ (Ω : Set (SpatialCoordinates d))) (hWm : MeasurableSet W)
    (fn : ℕ → DomainL2 Ω) (f : DomainL2 Ω) (hconv : Tendsto fn atTop (𝓝 f))
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hUN : ∀ n, (fn n : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (Ω : Set (SpatialCoordinates d))] UN n)
    (hU : (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (Ω : Set (SpatialCoordinates d))] U) :
    Tendsto (fun n => normalizedL2On W (fun x => UN n x - U x)) atTop (𝓝 0) := by
  apply Section6TheoremCUncut.tendsto_normalizedL2On_of_tendsto_integral_sq
  have hnorm : Tendsto (fun n => ‖fn n - f‖ ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_iff_norm_sub_tendsto_zero.mp hconv).pow 2
    simpa only [zero_pow two_ne_zero] using h
  refine squeeze_zero (fun n => setIntegral_nonneg hWm (fun x _ => sq_nonneg _))
    (fun n => ?_) hnorm
  rw [domainL2_norm_sq_eq_integral]
  have hae : (fun x => ((fn n - f : DomainL2 Ω) x) ^ 2) =ᵐ[volume.restrict
      (Ω : Set (SpatialCoordinates d))] fun x => (UN n x - U x) ^ 2 := by
    filter_upwards [Lp.coeFn_sub (fn n) f, hUN n, hU] with x hx h1 h2
    rw [hx, Pi.sub_apply, h1, h2]
  rw [integral_congr_ae hae]
  have hint : IntegrableOn (fun x => (UN n x - U x) ^ 2) (Ω : Set (SpatialCoordinates d)) :=
    (((Lp.memLp (fn n - f)).integrable_sq).congr hae)
  exact setIntegral_mono_set hint
    (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hWΩ)

/-- Centered normalized `L²` oscillations on a subwindow converge along `L²(Ω)`
convergence. -/
theorem tendsto_centered_normalizedL2_of_tendsto_domainL2 {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (W : Set (SpatialCoordinates d))
    (hWΩ : W ⊆ (Ω : Set (SpatialCoordinates d))) (hWm : MeasurableSet W)
    (hWpos : 0 < (volume W).toReal) (hWtop : volume W ≠ ⊤)
    (fn : ℕ → DomainL2 Ω) (f : DomainL2 Ω) (hconv : Tendsto fn atTop (𝓝 f))
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hUN : ∀ n, (fn n : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (Ω : Set (SpatialCoordinates d))] UN n)
    (hU : (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (Ω : Set (SpatialCoordinates d))] U) :
    Tendsto (fun n => normalizedL2On W
      (fun x => UN n x - (volume.real W)⁻¹ * ∫ y in W, UN n y)) atTop
      (𝓝 (normalizedL2On W (fun x => U x - (volume.real W)⁻¹ * ∫ y in W, U y))) := by
  haveI : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.mpr hWtop
  have hmemN : ∀ n, MemLp (UN n) 2 (volume.restrict W) := fun n =>
    ((Lp.memLp (fn n)).ae_eq (hUN n)).mono_measure (Measure.restrict_mono hWΩ le_rfl)
  have hmem : MemLp U 2 (volume.restrict W) :=
    ((Lp.memLp f).ae_eq hU).mono_measure (Measure.restrict_mono hWΩ le_rfl)
  have hraw := tendsto_normalizedL2On_sub_of_tendsto_domainL2 W hWΩ hWm fn f hconv UN U hUN hU
  have hcent := Section6TheoremC.tendsto_centeredNormalizedL2On_sub_of_tendsto_sub hWm hWpos
    hWtop hmemN hmem hraw
  exact Section6TheoremC.tendsto_normalizedL2On_of_tendsto_sub
    (fun n => (hmemN n).sub (memLp_const _)) (hmem.sub (memLp_const _)) hcent

end SubdiffusiveProcess
