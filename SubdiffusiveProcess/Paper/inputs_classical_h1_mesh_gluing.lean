module

public import SubdiffusiveProcess.Lane2.MeshGeometry
public import SubdiffusiveProcess.Sobolev.NativeH10Reverse
public import SubdiffusiveProcess.Geometry.ClosedOddGridCover
public import SubdiffusiveProcess.Gluing.Assembly

@[expose] public section

/-! Classical Sobolev trace gluing on a finite cubical partition.
Matching continuous traces and zero exterior trace give an H1-zero function.
This is independent of coefficients, random fields, and limiting forms.
Reference: J. Schöberl, Interactive Finite Elements, Section 15.2,
https://jschoeberl.github.io/iFEM/sobolevspaces/Traces.html#sobolev-spaces-over-sub-domains
and the zero-trace characterization immediately before Section 15.1.
-/
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
noncomputable section
namespace Paper

/-- Continuous native Sobolev functions with matching cell traces and zero outer trace glue to an H1-zero function. -/
theorem inputs_classical_h1_mesh_gluing
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
    (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)), g x = 0)
    (uc : ∀ k : OddGridIndex d (triadicHalf J),
      H1Function (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)))
    (hcont : ∀ k, ContinuousOn (uc k).toFun
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))))
    (htrace : ∀ k, ∀ x ∈ frontier
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)), (uc k).toFun x = g x) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (∀ k, EqOn w.toH1Function.toFun (uc k).toFun
        (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)))) ∧
      ∀ k i, (fun x => w.toH1Function.grad x i) =ᵐ[volume.restrict
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))]
          (fun x => (uc k).grad x i) := by
  have hrad : ∀ k : OddGridIndex d (triadicHalf J), 0 < R / (2 * ((triadicHalf J : ℕ) : ℝ) + 1) :=
    fun _ => div_pos hR (by positivity)
  exact SubdiffusiveProcess.Gluing.h1_glue z R hR
    (oddGridCenter z R (triadicHalf J)) (fun _ => R / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) hrad
    (fun k => oddGridCell_subset z hR (triadicHalf J) k)
    (oddGridCell_pairwiseDisjoint z hR (triadicHalf J))
    (oddGridCell_closure_iUnion_eq_closure_centeredCube z hR (triadicHalf J))
    g hg0 uc hcont htrace

end Paper
