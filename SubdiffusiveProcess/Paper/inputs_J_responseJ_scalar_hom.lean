import SubdiffusiveProcess.Paper.in_J

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_J_responseJ_scalar_hom (d : ℕ) (hd : 2 ≤ d) :
    (∀ (U : Homogenization.Book.Ch02.Domain d)
      (a b : Homogenization.Book.Ch02.CoeffOn U) (a0 : ℝ), 0 < a0 →
      (∀ x : Homogenization.Vec d, b.toCoeffField x = a0⁻¹ • a.toCoeffField x) →
      ∀ e : Homogenization.Vec d,
      Homogenization.Book.Ch02.responseJ U a
          ((Real.sqrt a0)⁻¹ • e) (Real.sqrt a0 • e) =
        Homogenization.Book.Ch02.responseJ U b e e) := by
  intro U a b a0 ha0 hab e
  have hcoeff : b.toCoeffField = a0⁻¹ • a.toCoeffField := by
    funext x
    exact hab x
  have hc : 0 < a0⁻¹ := inv_pos.mpr ha0
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ U a
    ((Real.sqrt a0)⁻¹ • e) (Real.sqrt a0 • e),
    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ U b e e,
    hcoeff]
  have hhom := Homogenization.responseJ_homogeneous_coeffField
    (U : Set (Homogenization.Vec d)) e e a.toCoeffField hc
  have hsqrt : Real.sqrt (a0⁻¹) = (Real.sqrt a0)⁻¹ := by
    rw [Real.sqrt_inv]
  have hsqrt_inv : (Real.sqrt (a0⁻¹))⁻¹ = Real.sqrt a0 := by
    rw [hsqrt, inv_inv]
  simpa [hsqrt, hsqrt_inv] using hhom.symm

end Paper
