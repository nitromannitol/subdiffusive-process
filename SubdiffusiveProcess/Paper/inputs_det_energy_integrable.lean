import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Analysis.ScalarEnergyTransport

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_det_energy_integrable (d : ℕ) (a : Vec d → ℝ) (y : Vec d)
    (data : ScalarTriadicCoeffData (fun q => a (q + y))) (k : ℤ)
    (u0 : H1Function (openCubeSet (originCube d k)))
    (G : Vec d → Vec d) (hG : ∀ q, u0.grad q = G (q + y)) :
    (IntegrableOn (fun q => a (q + y) * vecNormSq (G (q + y)))
      (cubeSet (originCube d k)) volume) := by
  have h := SubdiffusiveProcess.ScalarEnergyTransport.integrable_energy
    (originCube d k) (data.onCube (originCube d k)) u0
  simpa only [hG] using h

end Paper

