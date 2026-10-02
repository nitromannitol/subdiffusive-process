import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ScalarDivergenceLift
import Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingDefinitions

/-!
# Scalar-forcing entry into the Chapter 3 coarse-graining carrier

Once a scalar datum has a weak divergence lift, the scalar Dirichlet equation
is literally the heterogeneous or scalar `IsForcedEquation` used by general
coarse graining.  Two solutions with the same boundary datum also have the
required `H¹₀` difference.  These are carrier conversions only.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- A scalar weak Dirichlet equation enters the heterogeneous Chapter 3
forced-equation carrier after its coefficient spelling is identified. -/
theorem isForcedEquation_of_isScalarDirichletSolutionOn_of_pairing
    {d : ℕ} {Q : TriadicCube d}
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    {A : CoeffField d} {u h : H1Function (openCubeSet Q)}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (ha : a.toCoeffField = A)
    (hu : IsScalarDirichletSolutionOn A Q u h f)
    (hF : ∀ phi : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, f x * phi.toH1Function.toFun x ∂volume =
        -∫ x in openCubeSet Q,
          vecDot (F x) (phi.toH1Function.grad x) ∂volume) :
    IsForcedEquation Q a u F := by
  intro phi
  rw [ha]
  exact (hu.2 phi).trans (hF phi)

/-- Constant-scalar counterpart of
`isForcedEquation_of_isScalarDirichletSolutionOn_of_pairing`. -/
theorem isScalarForcedEquation_of_isScalarDirichletSolutionOn_of_pairing
    {d : ℕ} {Q : TriadicCube d} {sigma : ℝ}
    {u h : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    {F : Vec d → Vec d}
    (hu : IsScalarDirichletSolutionOn
      (fun _ ↦ scalarMatrix (d := d) sigma) Q u h f)
    (hF : ∀ phi : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, f x * phi.toH1Function.toFun x ∂volume =
        -∫ x in openCubeSet Q,
          vecDot (F x) (phi.toH1Function.grad x) ∂volume) :
    IsScalarForcedEquation Q sigma u F := by
  intro phi
  exact (hu.2 phi).trans (hF phi)

/-- Solutions carrying the same boundary datum have the `H¹₀` difference
required by general coarse graining. -/
theorem hasH10Difference_of_hasZeroTraceDifferenceOn
    {d : ℕ} {Q : TriadicCube d}
    {u v h : H1Function (openCubeSet Q)}
    (hu : HasZeroTraceDifferenceOn (openCubeSet Q) u h)
    (hv : HasZeroTraceDifferenceOn (openCubeSet Q) v h) :
    HasH10Difference Q u v := by
  obtain ⟨wu, huValue, _huGrad⟩ := hu
  obtain ⟨wv, hvValue, _hvGrad⟩ := hv
  refine ⟨wu - wv, Filter.Eventually.of_forall fun x ↦ ?_⟩
  change (wu.toH1Function + (-wv.toH1Function)).toFun x =
    u.toFun x - v.toFun x
  simp only [H1Function.add_toFun, H1Function.neg_toFun]
  rw [huValue x, hvValue x]
  ring

/-- One-term specialization for two scalar Dirichlet solutions sharing the
same boundary datum. -/
theorem hasH10Difference_of_scalarDirichletSolutions
    {d : ℕ} {Q : TriadicCube d} {A B : CoeffField d}
    {u v h : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (hu : IsScalarDirichletSolutionOn A Q u h f)
    (hv : IsScalarDirichletSolutionOn B Q v h f) :
    HasH10Difference Q u v :=
  hasH10Difference_of_hasZeroTraceDifferenceOn hu.1 hv.1

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
