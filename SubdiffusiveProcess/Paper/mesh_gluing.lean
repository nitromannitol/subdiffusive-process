import SubdiffusiveProcess.Lane2.MeshGluing
import SubdiffusiveProcess.Lane2.CellAssembly
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.MeshError
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff Distributions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}



theorem mesh_gluing [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a)
    (lam Lam : ℝ) (hlam : 0 < lam)
    (habounds : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam)
    (φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ.toFun)
    (hφsupp : HasCompactSupport φ.toFun)
    (hφQ : tsupport φ.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (uc : ∀ k : OddGridIndex d (triadicHalf J),
      H1Function (oddGridCell z R hR (triadicHalf J) k :
        Set (SpatialCoordinates d)))
    (hharm : ∀ k : OddGridIndex d (triadicHalf J),
      IsWeaklyHarmonicOn a
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
        (uc k))
    (htrace : ∀ k : OddGridIndex d (triadicHalf J),
      HasZeroTraceDifferenceOn
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
        (uc k)
        (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
          (oddGridCell_subset z hR (triadicHalf J) k))) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      (∀ k : OddGridIndex d (triadicHalf J),
        ∀ᵐ x ∂(volume.restrict (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d))),
          w.toH1Function.toFun x = (uc k).toFun x) ∧
      ContinuousOn w.toH1Function.toFun
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (∀ k : OddGridIndex d (triadicHalf J),
        ∀ x ∈ frontier (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d)),
          w.toH1Function.toFun x = φ.toFun x) ∧
      energy a (centeredCube z R hR : Set (SpatialCoordinates d))
          w.toH1Function =
        (∑ k : OddGridIndex d (triadicHalf J),
          energy a (oddGridCell z R hR (triadicHalf J) k :
            Set (SpatialCoordinates d)) (uc k)) ∧
      (∀ k : OddGridIndex d (triadicHalf J),
        energy a (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d)) (uc k)
          = sInf {e : ℝ | ∃ v : H1Function
              (oddGridCell z R hR (triadicHalf J) k :
                Set (SpatialCoordinates d)),
            HasZeroTraceDifferenceOn
              (oddGridCell z R hR (triadicHalf J) k :
                Set (SpatialCoordinates d)) v
              (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
                (oddGridCell_subset z hR (triadicHalf J) k)) ∧
            e = energy a (oddGridCell z R hR (triadicHalf J) k :
              Set (SpatialCoordinates d)) v}) :=
  lane2_meshGluing hd z R hR J a ha lam Lam hlam habounds φ hφ hφsupp hφQ
    uc hharm htrace

end Paper
