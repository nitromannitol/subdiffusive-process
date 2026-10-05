module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeOccupationTorsion
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeMeanExitLower

@[expose] public section

/-!
# Pointwise readout of a good-cube torsion lower bound

The analytic estimate is first proved almost everywhere for an `H10Function`.
The local diffusion datum and the semigroup transfer give it at every point
of an open interior set, including the middle quarter used by the anchor.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- An almost-everywhere lower bound for the zero-trace torsion carrier gives
an exit-time lower bound at every point of an open interior set. -/
theorem goodCube_meanExit_lower_of_h10
    {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law) {U V : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hV : IsOpen V) (hVU : V ⊆ U) (v : H10Function U)
    (hv : ∀ᵐ y ∂volume.restrict U,
      ENNReal.ofReal (v.toH1Function.toFun y) = meanExit law U y)
    {k : ℝ} (hk : 0 ≤ k)
    (hlower : ∀ᵐ y ∂volume.restrict U, y ∈ V → k ≤ v.toH1Function.toFun y) :
    ∀ x ∈ V, ENNReal.ofReal k ≤ meanExit law U x := by
  apply goodCube_meanExit_lower_of_ae_on_open hD hU hUb hV hVU hk
  have hAc := SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration.weightedMeasure_restrict_absolutelyContinuous_volume_restrict
      (rho := rho) hU.measurableSet
  apply hAc.ae_le
  filter_upwards [hv, hlower] with y hye hyl
  intro hyV
  rw [← hye]
  exact ENNReal.ofReal_le_ofReal (hyl hyV)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
