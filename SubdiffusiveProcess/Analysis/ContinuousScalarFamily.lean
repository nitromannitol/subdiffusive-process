module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFiniteSideConditions

@[expose] public section

/-! Continuous positive scalar coefficients admit compatible triadic carriers
and finite discounted homogenization errors. This packages existing coefficient
and finiteness suppliers; it asserts no smallness of the error.
-/
noncomputable section
namespace SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

/-- A continuous positive scalar field defines a compatible family on every triadic cube. -/
def continuousScalarFamily {d : ℕ} (a : Vec d → ℝ)
    (ha : Continuous a) (hpos : ∀ x, 0 < a x) : ScalarTriadicCoeffData a where
  onCube Q := Classical.choice
    (Section5Support.exists_scalarCoeffOnData_of_continuous_pos
      ha hpos (Book.Ch02.cubeDomain Q))

/-- Positive discount makes the scalar two-exponent homogenization error finite. -/
theorem scalarFamily_error_ne_top {d : ℕ} [NeZero d] {a : Vec d → ℝ}
    (data : ScalarTriadicCoeffData a) (s alpha : ℝ) (hs : 0 < s) (ha : 0 < alpha) :
    paperHomogenizationError (originCube d 0) 0 s
      Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily alpha ≠ ⊤ :=
  Section8Resolvent.fluxRowFinite_paperHomogenizationError_two_ne_top
    (originCube d 0) (by rfl) hs data.toTriadicCoeffFamily
      (fun Q => (data.onCube Q).isSymmetric) ha

end SubdiffusiveProcess
