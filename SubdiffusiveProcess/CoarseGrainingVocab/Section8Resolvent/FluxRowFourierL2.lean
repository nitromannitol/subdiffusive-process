module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section




open MeasureTheory
open scoped FourierTransform

noncomputable section

namespace SubdiffusiveProcess.Section8Resolvent.FluxRowFourier

/-- Euclidean `d`-space over the reals. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Complex-valued `L²` on Euclidean `d`-space. -/
abbrev EuclideanL2 (d : ℕ) :=
  Lp ℂ 2 (volume : Measure (Vec d))

/-- Schwartz functions have dense image in Euclidean `L²`. -/
theorem denseRange_schwartzToEuclideanL2 (d : ℕ) :
    DenseRange
      (SchwartzMap.toLpCLM ℂ ℂ 2
        (volume : Measure (Vec d))) := by
  convert!
    (SchwartzMap.denseRange_toLpCLM (E := Vec d)
      (F := ℂ) (μ := volume) (p := 2) (by simp)) using 1 <;> rfl

/-- The Fourier transform on Euclidean `L²`, obtained by extending its
Schwartz-space Plancherel isometry through the dense Schwartz embedding. -/
def euclideanL2FourierTransform (d : ℕ) : EuclideanL2 d ≃ₗᵢ[ℂ] EuclideanL2 d :=
  (FourierTransform.fourierCLE ℂ (SchwartzMap (Vec d) ℂ)).toLinearEquiv.extendOfIsometry
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
    (denseRange_schwartzToEuclideanL2 d)
    (denseRange_schwartzToEuclideanL2 d)
    (fun f ↦ SchwartzMap.norm_fourier_toL2_eq f)

/-- On Schwartz functions, the extended transform is the classical Fourier
transform, regarded as an `L²` class. -/
@[simp] theorem euclideanL2FourierTransform_schwartz (d : ℕ)
    (f : SchwartzMap (Vec d) ℂ) :
    euclideanL2FourierTransform d (f.toLp 2 volume) = (𝓕 f).toLp 2 volume := by
  exact LinearEquiv.extendOfIsometry_eq
    (FourierTransform.fourierCLE ℂ (SchwartzMap (Vec d) ℂ)).toLinearEquiv
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
    (denseRange_schwartzToEuclideanL2 d)
    (denseRange_schwartzToEuclideanL2 d)
    (fun g ↦ SchwartzMap.norm_fourier_toL2_eq g) f

/-- The inverse `L²` Fourier transform. -/
def euclideanL2FourierTransformInv (d : ℕ) : EuclideanL2 d ≃ₗᵢ[ℂ] EuclideanL2 d :=
  (euclideanL2FourierTransform d).symm

@[simp] theorem euclideanL2FourierTransformInv_schwartz (d : ℕ)
    (f : SchwartzMap (Vec d) ℂ) :
    euclideanL2FourierTransformInv d (f.toLp 2 volume) = (𝓕⁻ f).toLp 2 volume := by
  exact LinearEquiv.extendOfIsometry_symm_eq
    (FourierTransform.fourierCLE ℂ (SchwartzMap (Vec d) ℂ)).toLinearEquiv
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
    (denseRange_schwartzToEuclideanL2 d)
    (denseRange_schwartzToEuclideanL2 d)
    (fun g ↦ SchwartzMap.norm_fourier_toL2_eq g) f

theorem euclideanL2FourierTransform_norm (d : ℕ) (f : EuclideanL2 d) :
    ‖euclideanL2FourierTransform d f‖ = ‖f‖ :=
  (euclideanL2FourierTransform d).norm_map f

@[simp] theorem euclideanL2FourierTransformInv_apply_transform (d : ℕ)
    (f : EuclideanL2 d) :
    euclideanL2FourierTransformInv d (euclideanL2FourierTransform d f) = f :=
  (euclideanL2FourierTransform d).symm_apply_apply f

@[simp] theorem euclideanL2FourierTransform_apply_inv (d : ℕ)
    (f : EuclideanL2 d) :
    euclideanL2FourierTransform d (euclideanL2FourierTransformInv d f) = f :=
  (euclideanL2FourierTransform d).apply_symm_apply f

end SubdiffusiveProcess.Section8Resolvent.FluxRowFourier
