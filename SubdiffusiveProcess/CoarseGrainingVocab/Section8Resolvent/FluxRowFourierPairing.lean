module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFourierL2

@[expose] public section

/-!
# Weak characterization of the Euclidean `L²` Fourier transform

The extended transform is characterized by its pairing with Schwartz test
functions.  This is the form needed to compare it with the classical Fourier
integral on `L¹ ∩ L²`; compare
-/

open MeasureTheory
open scoped FourierTransform ComplexInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.Section8Resolvent.FluxRowFourier

/-- The `L²` Fourier transform has the expected weak pairing against every
Schwartz function. -/
theorem inner_euclideanL2FourierTransform (d : ℕ)
    (g : SchwartzMap (Vec d) ℂ) (f : EuclideanL2 d) :
    inner ℂ (g.toLp 2 volume) (euclideanL2FourierTransform d f) =
      inner ℂ ((𝓕⁻ g).toLp 2 volume) f := by
  refine (denseRange_schwartzToEuclideanL2 d).induction ?_ ?_ f
  · rintro _ ⟨h, rfl⟩
    change inner ℂ (g.toLp 2 volume)
      (euclideanL2FourierTransform d (h.toLp 2 volume)) =
        inner ℂ ((𝓕⁻ g).toLp 2 volume) (h.toLp 2 volume)
    rw [euclideanL2FourierTransform_schwartz]
    simpa using SchwartzMap.inner_fourier_toL2_eq (𝓕⁻ g) h
  · exact isClosed_eq (by fun_prop) (by fun_prop)

/-- The corresponding weak pairing formula for the inverse transform. -/
theorem inner_euclideanL2FourierTransformInv (d : ℕ)
    (g : SchwartzMap (Vec d) ℂ) (f : EuclideanL2 d) :
    inner ℂ (g.toLp 2 volume) (euclideanL2FourierTransformInv d f) =
      inner ℂ ((𝓕 g).toLp 2 volume) f := by
  have h := inner_euclideanL2FourierTransform d (𝓕 g)
    (euclideanL2FourierTransformInv d f)
  simpa using h.symm

end SubdiffusiveProcess.Section8Resolvent.FluxRowFourier
