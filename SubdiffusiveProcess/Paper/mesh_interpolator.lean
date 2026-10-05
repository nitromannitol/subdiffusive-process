module

public import SubdiffusiveProcess.VariationalResponses.MeshGluing
public import SubdiffusiveProcess.Geometry.TriadicResidual
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6MeasurableMaxPrinciple
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeshGluing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
@[expose] public section

open SubdiffusiveProcess
open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The target `exists_harmonicTriadicMeshInterpolator` is the harmonic triadic mesh interpolator in the context of `mfd:sec-local-form`. Supplied by: `SubdiffusiveProcess.lane2_meshInterpolator` (`SubdiffusiveProcess/VariationalResponses/MeshGluing.lean`). The cellwise Dirichlet minimisers are `lane2_exists_weaklyHarmonic_of_zeroTrace` on each cell (an open bounded convex domain), they are glued by `mesh_gluing`, the three cellwise clauses transfer from the minimisers to the glued datum across the almost-everywhere identification (the zero-trace witness is re-based on the glued datum's own value and gradient so that the identities are pointwise, as the predicate demands), and the pointwise clause is `lane2_mesh_cell_error` on each open cell carried to every point of the cube by continuity, the cells' union being dense in it. -/
theorem mesh_interpolator
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
        (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ),
        0 < lam →
        Continuous a →
        (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
          lam ≤ a x ∧ a x ≤ Lam) →
        ∀ φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)),
          ContDiff ℝ ∞ φ.toFun →
          HasCompactSupport φ.toFun →
          tsupport φ.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
          ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
            ContinuousOn w.toH1Function.toFun
              (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
            (∀ k : OddGridIndex d (triadicHalf J),
              let W := oddGridCell z R hR (triadicHalf J) k
              let hW : (W : Set (SpatialCoordinates d)) ⊆
                  (centeredCube z R hR : Set (SpatialCoordinates d)) :=
                oddGridCell_subset z hR (triadicHalf J) k
              let wk : H1Function (W : Set (SpatialCoordinates d)) :=
                w.toH1Function.restrict W.isOpen hW
              let φk : H1Function (W : Set (SpatialCoordinates d)) :=
                φ.restrict W.isOpen hW
              IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) wk ∧
              HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) wk φk ∧
              energy a (W : Set (SpatialCoordinates d)) wk =
                sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
                  HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
                  e = energy a (W : Set (SpatialCoordinates d)) u}) ∧
            energy a (centeredCube z R hR : Set (SpatialCoordinates d))
                w.toH1Function =
              (∑ k : OddGridIndex d (triadicHalf J),
                let W := oddGridCell z R hR (triadicHalf J) k
                let hW : (W : Set (SpatialCoordinates d)) ⊆
                    (centeredCube z R hR : Set (SpatialCoordinates d)) :=
                  oddGridCell_subset z hR (triadicHalf J) k
                let φk : H1Function (W : Set (SpatialCoordinates d)) :=
                  φ.restrict W.isOpen hW
                sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
                  HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
                  e = energy a (W : Set (SpatialCoordinates d)) u}) ∧
            (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
              |w.toH1Function.toFun x - φ.toFun x| ≤
                C * (R / (3 : ℝ) ^ J) *
                  sSup ((fun y => ‖fderiv ℝ φ.toFun y‖) ''
                    closure (centeredCube z R hR : Set (SpatialCoordinates d)))) :=
  lane2_meshInterpolator hd

end SubdiffusiveProcess.Paper
