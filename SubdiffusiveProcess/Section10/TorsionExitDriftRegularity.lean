module

public import SubdiffusiveProcess.Section10.TorsionExitMartingaleProblem
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-! The literal reversible drift has the local Lipschitz regularity needed
by classical diffusion theorems. This follows from the source's actual compact
derivative certificates; no additional coefficient smoothness is requested. -/

noncomputable section
open Homogenization Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
namespace SubdiffusiveProcess.Section10

/-- The actual `C¹,¹` certificate controls the full Fréchet derivative locally. -/
theorem locallyLipschitz_fderiv_of_locallyC11 {d : ℕ} {a : Vec d → ℝ}
    (ha : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 a) :
    LocallyLipschitz (fderiv ℝ a) := by
  obtain ⟨Da, hDa, hLip⟩ := ha
  have hlocal : LocallyLipschitz Da := by
    intro x
    obtain ⟨C, hC⟩ := hLip (Metric.closedBall x 1) (isCompact_closedBall x 1)
    exact ⟨C, Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
      hC.mono Metric.ball_subset_closedBall⟩
  have heq : fderiv ℝ a = Da := funext fun x ↦ (hDa x).fderiv
  rwa [heq]

/-- No `C²` coefficient assumption is used to obtain the source drift. -/
theorem locallyLipschitz_reversibleDrift {d : ℕ} {a : Vec d → ℝ}
    (hapos : ∀ x, 0 < a x) (ha : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 a) :
    LocallyLipschitz (reversibleDrift a) := by
  have hinv : LocallyLipschitz (fun x ↦ (a x)⁻¹) :=
    ((contDiff_one_of_locallyC11 ha).inv fun x ↦ (hapos x).ne').locallyLipschitz
  have hDa := locallyLipschitz_fderiv_of_locallyC11 ha
  have hsmul : LocallyLipschitz
      (fun x ↦ (a x)⁻¹ • fderiv ℝ a x) :=
    (contDiff_smul (𝕜 := ℝ) (n := 1)).locallyLipschitz.comp (hinv.prodMk hDa)
  let eval : (Vec d →L[ℝ] ℝ) →L[ℝ] Vec d :=
    ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.apply ℝ ℝ (basisVec i)
  have h := eval.lipschitz.locallyLipschitz.comp hsmul
  have heq : eval ∘ (fun x ↦ (a x)⁻¹ • fderiv ℝ a x) = reversibleDrift a := by
    funext x i
    change (a x)⁻¹ * (fderiv ℝ a x) (basisVec i) =
      euclideanCoordDeriv i a x / a x
    simp only [euclideanCoordDeriv, div_eq_mul_inv, mul_comm]
  rwa [heq] at h

end SubdiffusiveProcess.Section10
