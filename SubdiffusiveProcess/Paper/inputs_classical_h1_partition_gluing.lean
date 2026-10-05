module

public import SubdiffusiveProcess.VariationalResponses.MeshGeometry
public import SubdiffusiveProcess.Sobolev.NativeH10Reverse
public import SubdiffusiveProcess.Gluing.Assembly

@[expose] public section

/-! Classical Sobolev gluing over a finite cubical partition with unequal cell sizes.
Matching traces give the distributional gradient cell by cell; zero outer trace gives H10.
This statement contains no coefficient, limiting form, or quantitative extension bound.
Reference: Schöberl, Interactive Finite Elements, Section 15.2 and the zero-trace theorem,
https://jschoeberl.github.io/iFEM/sobolevspaces/Traces.html#sobolev-spaces-over-sub-domains.
-/
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Matching continuous Sobolev traces on a finite cubical partition glue to a killed Sobolev function. -/
theorem inputs_classical_h1_partition_gluing
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ)
    (hrad : ∀ i, 0 < rad i)
    (hsub : ∀ i, (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hdisj : Pairwise (fun i j => Disjoint
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
      (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d))))
    (hcover : (⋃ i, closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) =
      closure (centeredCube z R hR : Set (SpatialCoordinates d)))
    (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)), g x = 0)
    (uc : ∀ i, H1Function (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
    (hcont : ∀ i, ContinuousOn (uc i).toFun
      (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))))
    (htrace : ∀ i, ∀ x ∈ frontier
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)), (uc i).toFun x = g x) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (∀ i, EqOn w.toH1Function.toFun (uc i).toFun
        (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))) ∧
      ∀ i j, (fun x => w.toH1Function.grad x j) =ᵐ[volume.restrict
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))]
          (fun x => (uc i).grad x j) := by
  exact SubdiffusiveProcess.Gluing.h1_glue z R hR cent rad hrad hsub hdisj hcover g hg0 uc hcont
    htrace

end SubdiffusiveProcess.Paper
