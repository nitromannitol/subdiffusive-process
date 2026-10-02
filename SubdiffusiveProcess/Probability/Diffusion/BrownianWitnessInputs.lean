import SubdiffusiveProcess.Probability.Diffusion.HuntDensity
import SubdiffusiveProcess.Probability.Diffusion.HuntIdentity
import SubdiffusiveProcess.Probability.Diffusion.Witnesses




set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- **The Brownian killed densities, from the interior continuity alone.**  The fixed-horizon
Hunt identity is no longer a hypothesis: `brownian_hunt_identity` proves it. -/
theorem continuousKilledDensities_laplacianLaw_of_continuity (d : ℕ)
    (hC : BrownianHuntContinuity d) :
    Input.ContinuousKilledDensities (fun _ => (1 : ℝ)) (laplacianLaw d) :=
  continuousKilledDensities_laplacianLaw_of_hunt (brownian_hunt_identity d) hC



theorem localDiffusionData_laplacianLaw_of_two_inputs (d : ℕ)
    (hpart : BrownianVariationalIdentification d) (hC : BrownianHuntContinuity d) :
    LocalDiffusionData (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (laplacianLaw d) :=
  localDiffusionData_laplacianLaw_of_partForm_and_hunt hpart (brownian_hunt_identity d) hC

/-- The existence form, on the same two inputs. -/
theorem exists_localDiffusionData_const_of_two_inputs (d : ℕ)
    (hpart : BrownianVariationalIdentification d) (hC : BrownianHuntContinuity d) :
    ∃ law : Kernel (Vec d) (Path d),
      LocalDiffusionData (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) law :=
  ⟨laplacianLaw d, localDiffusionData_laplacianLaw_of_two_inputs d hpart hC⟩

end SubdiffusiveProcess.Probability.Diffusion
