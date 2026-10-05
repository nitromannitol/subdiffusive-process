module

public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Analysis.ScalarEnergyTransport

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_det_energy_integrable (d : ℕ) (a : Vec d → ℝ) (y : Vec d)
    (data : ScalarTriadicCoeffData (fun q => a (q + y))) (k : ℤ)
    (u0 : H1Function (openCubeSet (originCube d k)))
    (G : Vec d → Vec d) (hG : ∀ q, u0.grad q = G (q + y)) :
    (IntegrableOn (fun q => a (q + y) * vecNormSq (G (q + y)))
      (cubeSet (originCube d k)) volume) := by
  have h := SubdiffusiveProcess.ScalarEnergyTransport.integrable_energy
    (originCube d k) (data.onCube (originCube d k)) u0
  simpa only [hG] using h

end SubdiffusiveProcess.Paper

