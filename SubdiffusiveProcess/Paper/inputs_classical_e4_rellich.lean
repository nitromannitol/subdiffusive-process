import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Compactness.CubeFractionalRellich

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- E4: fractional Rellich compactness on any fixed cube. -/
theorem inputs_classical_e4_rellich (d : ℕ) (hd : 2 ≤ d)
    (s : Set.Ioo (0 : ℝ) 1) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : ℕ → DomainL2 (centeredCube z r hr)) (B : ℝ)
    (hfinite : ∀ n, cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v n) < ⊤)
    (hbound : ∀ n, cubeFractionalSqNorm hd z r hr s (v n) ≤ B) :
    ∃ (phi : ℕ → ℕ) (w : DomainL2 (centeredCube z r hr)),
      StrictMono phi ∧ Tendsto (fun n => v (phi n)) atTop (nhds w) := by
  exact exists_subseq_of_cubeFractionalSqNorm_bounded d hd s z r hr v B hfinite hbound

end Paper
