import SubdiffusiveProcess.Paper.stationary_family
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.CoarseGrainingVocab.Model
import SubdiffusiveProcess.Lane4.Bridge
import Homogenization.Book.Ch02.MultiscaleEllipticity
import Mathlib.Tactic

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem in_moments_family_transport (d : ℕ) (hd : 2 ≤ d) :
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
      ∃ family : ℕ → BilateralField d → TriadicCoeffFamily d,
        ∀ (N : ℕ) (ω : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
            ((family N ω).coeffOn Q).toCoeffField x =
              scalarMatrix
                (cutoffCoefficient model
                  (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x) := by
  classical
  intro _ _ model
  let data : ∀ (N : ℕ) (ω : BilateralField d),
      SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData
        (fun x => cutoffCoefficient model
          (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x) := fun N ω =>
    { onCube := fun Q =>
        Classical.choice
          (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
            (SubdiffusiveProcess.Lane4.cutoffCoefficient_continuous model
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N)
            (SubdiffusiveProcess.Lane4.cutoffCoefficient_pos model
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N)
            (Homogenization.Book.Ch02.cubeDomain Q)) }
  refine ⟨fun N ω => (data N ω).toTriadicCoeffFamily, ?_⟩
  intro N ω Q
  exact Filter.Eventually.of_forall (fun x => rfl)

end Paper
