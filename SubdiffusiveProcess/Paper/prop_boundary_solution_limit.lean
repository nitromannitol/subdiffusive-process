import SubdiffusiveProcess.Paper.conv_represented_sequence
import SubdiffusiveProcess.Paper.conv_represented_estimates
import SubdiffusiveProcess.Paper.prop_killed_inverse
import SubdiffusiveProcess.Paper.mesh_interpolator
import SubdiffusiveProcess.Paper.cell_boundary_continuity
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Main.CubeFractionalL2Norm
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem prop_boundary_solution_limit
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (EQ : _root_.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (b beta : SpatialCoordinates d → ℝ)
    (betaQ : H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetaQfun : betaQ.toFun = beta)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (uBar : DomainL2 (centeredCube z (3 * r) h3r))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hUNtrace : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      HasZeroTraceDifferenceOn
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k))
        (betaQ.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hUNcellcont : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ContinuousOn (UN n).toFun
        (closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d))))
    (hUNcellb : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ frontier (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
        (UN n).toFun x = beta x)
    (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (hHcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Hcell k)
    (hCellEnergy : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      energy (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)) ≤ Bcell k)
    (hCellHolder : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        ∀ y ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
          |(UN n).toFun x - (UN n).toFun y| ≤ Hcell k * dist x y ^ alpha) ∧
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        |(UN n).toFun x| ≤ Hcell k))
    (hLower : ∀ (vn : ℕ → S.space)
      (v : DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ f : DomainL2 (centeredCube z (3 * r) h3r),
        Tendsto (fun n => inner ℝ f (vn n).val.1) atTop
          (𝓝 (inner ℝ f v))) →
      EQ.toClosedForm.energy v ≤
        Filter.liminf (fun n =>
          (responseForm S (aC n) (vn n) (vn n) : EReal)) atTop)
    (hRecovery : ∀ v ∈ EQ.toClosedForm.domain, ∃ vn : ℕ → S.space,
      Tendsto (fun n => ((vn n).val.1,
        (responseForm S (aC n) (vn n) (vn n) : EReal))) atTop
        (𝓝 (v, EQ.toClosedForm.energy v))) :
    ∃ u0 : DomainL2 (centeredCube z (3 * r) h3r),
      Tendsto (fun n => (UNS n).val.1) atTop (𝓝 u0) := by
  exact ⟨uBar, hUNL2⟩


end Paper
