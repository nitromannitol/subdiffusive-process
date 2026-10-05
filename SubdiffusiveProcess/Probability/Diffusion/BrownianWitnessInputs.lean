module

public import SubdiffusiveProcess.Probability.Diffusion.HuntDensity
public import SubdiffusiveProcess.Probability.Diffusion.HuntIdentity
public import SubdiffusiveProcess.Probability.Diffusion.Witnesses

@[expose] public section

/-!
# The Brownian `LocalDiffusionData` witness, on two remaining inputs

`HuntDensity.localDiffusionData_laplacianLaw_of_partForm_and_hunt` states the constant
coefficient witness on three Brownian-specific inputs.  One of them,
`BrownianHuntIdentity d`, is now a theorem: `HuntIdentity.brownian_hunt_identity`.  This file
performs that substitution, so that

    LocalDiffusionData (fun _ => 1) (fun _ => 1) (laplacianLaw d)

rests on exactly two named propositions:

* `BrownianVariationalIdentification d` — package target (i): the variational resolvent of the
  Laplacian on a bounded open set agrees a.e. with the killed occupation integral of the
  constructed Brownian law;
* `BrownianHuntContinuity d` — package target (iii): joint continuity of the exit correction
  `huntCorrection U` on `Ioi 0 ×ˢ U ×ˢ U`, the starting point included.

Nothing here is an unconditional existence theorem; the two inputs are not inhabited.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open _root_.SubdiffusiveProcess.Model
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

/-- **The constant-coefficient witness, from exactly two remaining inputs.**  Target (ii) of the
Brownian-witness package is discharged, so `LocalDiffusionData 1 1 (laplacianLaw d)` now rests on

* `BrownianVariationalIdentification d` — target (i), the identification of the variational
  resolvent with the killed occupation integral, and
* `BrownianHuntContinuity d` — target (iii), joint interior continuity of the exit correction.
-/
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
