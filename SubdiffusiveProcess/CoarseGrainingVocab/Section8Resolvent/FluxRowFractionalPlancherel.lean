module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszFractionalComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFourierClassical

@[expose] public section

/-!
# Plancherel on `Vec d` for the `vecDot` Fourier pairing

The inverse transform `inverseFourierSchwartz` is the `VectorFourier`
integral against the bilinear pairing `vecDotLinear d` on
`Vec d = Fin d → ℝ`, a space which carries the supremum norm and therefore no
inner product instance.  The Euclidean `L²` Fourier transform built by the
flux-row argument lives on `EuclideanSpace ℝ (Fin d)`.  This file transports the
argument's `L¹ ∩ L²` Plancherel identity along the measure-preserving identity
`WithLp.ofLp`, in the `ENNReal` form used by the fractional comparison.

Source: `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open _root_.SubdiffusiveProcess.Section8
open scoped FourierTransform ENNReal

noncomputable section

/-- The Fourier integral on `Vec d` for the `vecDot` pairing. -/
def fluxRowFractionalFourier {d : ℕ} (f : Vec d → ℂ) : Vec d → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume (vecDotLinear d) f

theorem fluxRowFractionalFourier_apply {d : ℕ} (f : Vec d → ℂ) (w : Vec d) :
    fluxRowFractionalFourier f w =
      ∫ v, (Real.fourierChar (-(vecDot v w)) : ℂ) • f v := rfl

/-- The identity `EuclideanSpace ℝ (Fin d) → Vec d` is measure preserving. -/
theorem fluxRowFractional_measurePreserving_ofLp (d : ℕ) :
    MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d)
      volume volume :=
  PiLp.volume_preserving_ofLp (Fin d)

theorem fluxRowFractional_measurableEmbedding_ofLp (d : ℕ) :
    MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) :=
  (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding

theorem fluxRowFractional_inner_eq_vecDot (d : ℕ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ((innerₗ (EuclideanSpace ℝ (Fin d))) x) y =
      vecDot (WithLp.ofLp x) (WithLp.ofLp y) := by
  rw [innerₗ_apply_apply]
  simp [vecDot, PiLp.inner_apply, RCLike.inner_apply, mul_comm]


/-- Fourier transform of the transported function. -/
theorem fluxRowFractional_fourier_ofLp (d : ℕ) (f : Vec d → ℂ)
    (y : EuclideanSpace ℝ (Fin d)) :
    𝓕 (fun v : EuclideanSpace ℝ (Fin d) ↦ f (WithLp.ofLp v)) y =
      fluxRowFractionalFourier f (WithLp.ofLp y) := by
  have hmp := fluxRowFractional_measurePreserving_ofLp d
  have hemb := fluxRowFractional_measurableEmbedding_ofLp d
  have h := hmp.integral_comp hemb (fun w : Vec d ↦
      (Real.fourierChar (-(vecDot w (WithLp.ofLp y))) : ℂ) • f w)
  calc
    𝓕 (fun v : EuclideanSpace ℝ (Fin d) ↦ f (WithLp.ofLp v)) y =
        ∫ v : EuclideanSpace ℝ (Fin d),
          (Real.fourierChar (-(vecDot (WithLp.ofLp v) (WithLp.ofLp y))) : ℂ) •
            f (WithLp.ofLp v) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
      simp only []
      rw [fluxRowFractional_inner_eq_vecDot d v y]
      rfl
    _ = ∫ w : Vec d,
          (Real.fourierChar (-(vecDot w (WithLp.ofLp y))) : ℂ) • f w := h
    _ = fluxRowFractionalFourier f (WithLp.ofLp y) := rfl

/-- **Plancherel** for the `vecDot` Fourier integral on `Vec d`, for
functions in `L¹ ∩ L²`. -/
theorem fluxRowFractional_lintegral_enorm_sq_fourier {d : ℕ} (f : Vec d → ℂ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    ∫⁻ y, ‖fluxRowFractionalFourier f y‖ₑ ^ 2 ∂volume =
      ∫⁻ xi, ‖f xi‖ₑ ^ 2 ∂volume := by
  classical
  set e : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp with he
  have hmp := fluxRowFractional_measurePreserving_ofLp d
  have hemb := fluxRowFractional_measurableEmbedding_ofLp d
  set f' : EuclideanSpace ℝ (Fin d) → ℂ := fun v ↦ f (e v) with hf'
  have hf1' : Integrable f' volume := (hmp.integrable_comp_emb hemb).2 hf1
  have hf2' : MemLp f' 2 volume := hf2.comp_measurePreserving hmp
  have hFmem : MemLp (𝓕 f') 2 volume :=
    _root_.SubdiffusiveProcess.Section8Resolvent.FluxRowFourier.classicalFourier_memLp_two d f' hf1' hf2'
  -- Plancherel in `eLpNorm` form on Euclidean space
  have hnorm : eLpNorm (𝓕 f') 2 volume = eLpNorm f' 2 volume := by
    have hEq := _root_.SubdiffusiveProcess.Section8Resolvent.FluxRowFourier.euclideanL2FourierTransform_toLp_eq_classical
      d f' hf1' hf2'
    have h1 : ‖_root_.SubdiffusiveProcess.Section8Resolvent.FluxRowFourier.euclideanL2FourierTransform d
        (hf2'.toLp f')‖ = ‖hFmem.toLp (𝓕 f')‖ := by rw [hEq]
    rw [_root_.SubdiffusiveProcess.Section8Resolvent.FluxRowFourier.euclideanL2FourierTransform_norm,
      Lp.norm_toLp, Lp.norm_toLp] at h1
    exact (ENNReal.toReal_eq_toReal_iff' hFmem.eLpNorm_ne_top hf2'.eLpNorm_ne_top).1 h1.symm
  -- turn `eLpNorm` into the squared `lintegral`
  have hsq : ∀ g : EuclideanSpace ℝ (Fin d) → ℂ,
      ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) =
        (SubdiffusiveProcess.RawLp.eLpNorm g 2 volume) ^ (2 : ℕ) := by
    intro g
    have h := lintegral_rpow_enorm_eq_rpow_eLpNorm'
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (f := g)
      (show (0:ℝ) < 2 by norm_num)
    simp only [SubdiffusiveProcess.RawLp.eLpNorm, ite_eq_right (show (2 : ℝ≥0∞) ≠ 0 by norm_num),
      ite_eq_right (show (2 : ℝ≥0∞) ≠ ∞ by norm_num)]
    simp only [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]
    push_cast
    exact h
  have hmain : ∫⁻ y, ‖𝓕 f' y‖ₑ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) =
      ∫⁻ xi, ‖f' xi‖ₑ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    rw [hsq, hsq, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hFmem.aestronglyMeasurable,
      SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf2'.aestronglyMeasurable, hnorm]
  have hleft : ∫⁻ y, ‖fluxRowFractionalFourier f y‖ₑ ^ 2 ∂volume =
      ∫⁻ y, ‖𝓕 f' y‖ₑ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    rw [← hmp.lintegral_comp_emb hemb
      (fun w : Vec d ↦ ‖fluxRowFractionalFourier f w‖ₑ ^ 2)]
    exact lintegral_congr fun v ↦ by rw [fluxRowFractional_fourier_ofLp d f v]
  have hright : ∫⁻ xi, ‖f xi‖ₑ ^ 2 ∂volume =
      ∫⁻ xi, ‖f' xi‖ₑ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    rw [← hmp.lintegral_comp_emb hemb (fun w : Vec d ↦ ‖f w‖ₑ ^ 2)]
  rw [hleft, hright, hmain]


/-- The squared `L²` seminorm as a lower Lebesgue integral. -/
theorem fluxRowFractional_eLpNorm_two_sq {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (g : X → ℂ) :
    (SubdiffusiveProcess.RawLp.eLpNorm g 2 mu) ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂mu := by
  have h := lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := mu) (f := g)
    (show (0 : ℝ) < 2 by norm_num)
  simp only [SubdiffusiveProcess.RawLp.eLpNorm, ite_eq_right (show (2 : ℝ≥0∞) ≠ 0 by norm_num),
    ite_eq_right (show (2 : ℝ≥0∞) ≠ ∞ by norm_num)]
  simp only [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]
  push_cast
  exact h.symm


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
