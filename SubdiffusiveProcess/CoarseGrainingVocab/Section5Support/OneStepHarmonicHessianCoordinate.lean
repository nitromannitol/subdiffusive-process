module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHarmonicHighExponentRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHessianRowNormalization

@[expose] public section

/-!
# High-exponent localization of one harmonic Hessian coordinate
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- One weak-Hessian coordinate inherits the fixed `L^(16d)` interior gain
from a normalized total first-child Hessian estimate. -/
theorem harmonic_hessian_coordinate_highExponent_bound
    {d : ℕ} (hd : 3 ≤ d) (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q))
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hS : WeakPoissonEquationOn (scaledOpenCubeSet Q (1 / 2 : ℝ))
      uS (fun _ => 0)) (A : ℝ)
    (henergy : cubeScaleFactor (CubeCalderonZygmund.centralChild Q) *
      ∑ a : Fin d, ∑ b : Fin d,
        cubeLpNorm (CubeCalderonZygmund.centralChild Q) 2
          (fun x => H.hess a b x) ≤
      A * ∑ k : Fin d, cubeLpNorm Q 2 (fun x => u.grad x k))
    (i j : Fin d) :
    MemLp (fun x => H.hess i j x)
        (oneStepHarmonicExponent d hd).exponent
        (normalizedCubeMeasure
          (CubeCalderonZygmund.centralDescendant
            (CubeCalderonZygmund.centralChild Q)
            (oneStepHarmonicGainDepth d hd))) ∧
      cubeLpNorm
          (CubeCalderonZygmund.centralDescendant
            (CubeCalderonZygmund.centralChild Q)
            (oneStepHarmonicGainDepth d hd))
          (oneStepHarmonicExponent d hd).exponent
          (fun x => H.hess i j x) ≤
        (3 * oneStepHarmonicGainConstant d hd * A) *
          (cubeScaleFactor Q)⁻¹ *
            ∑ k : Fin d, cubeLpNorm Q 2 (fun x => u.grad x k) := by
  let P : TriadicCube d := CubeCalderonZygmund.centralChild Q
  have hPsub : openCubeSet P ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) :=
    (openCubeSet_subset_cubeSet P).trans (by
      simpa [P] using
        CubeCalderonZygmund.centralChild_cubeSet_subset_scaledOpenInnerHalf Q)
  let HP : HasWeakHessianOn (openCubeSet P)
      (uS.restrict (isOpen_openCubeSet P) hPsub) :=
    H.restrict (isOpen_openCubeSet P) hPsub
  let v : H1Function (openCubeSet P) := HP.gradCoordH1Function i
  have hvS : WeakPoissonEquationOn (scaledOpenCubeSet Q (1 / 2 : ℝ))
      (H.gradCoordH1Function i) (fun _ => 0) :=
    hS.gradCoordH1Function_harmonic (isOpen_scaledOpenCubeSet Q _) H i
  have hvEq : v = (H.gradCoordH1Function i).restrict
      (isOpen_openCubeSet P) hPsub := by
    apply H1Function.ext <;> rfl
  have hv : WeakPoissonEquationOn (openCubeSet P) v (fun _ => 0) := by
    rw [hvEq]
    exact hvS.restrict (isOpen_openCubeSet P) hPsub
  have hgain := oneStepHarmonic_gain_row_bound d hd P v hv j
  have hgainHP :
      MemLp (fun x => HP.hess i j x)
          (oneStepHarmonicExponent d hd).exponent
          (normalizedCubeMeasure
            (CubeCalderonZygmund.centralDescendant P
              (oneStepHarmonicGainDepth d hd))) ∧
        cubeLpNorm
            (CubeCalderonZygmund.centralDescendant P
              (oneStepHarmonicGainDepth d hd))
            (oneStepHarmonicExponent d hd).exponent
            (fun x => HP.hess i j x) ≤
          oneStepHarmonicGainConstant d hd *
            ∑ k : Fin d, cubeLpNorm P 2 (fun x => HP.hess i k x) := by
    simpa only [v, HasWeakHessianOn.gradCoordH1Function_grad_apply] using! hgain
  have hHPH : ∀ a b : Fin d, ∀ x : Vec d,
      HP.hess a b x = H.hess a b x := by
    intro a b x
    rfl
  simp_rw [hHPH] at hgainHP
  refine ⟨by simpa [P] using hgainHP.1, ?_⟩
  have hnormalized := hessian_row_normalized_bound_of_total Q H.hess A
    (∑ k : Fin d, cubeLpNorm Q 2 (fun x => u.grad x k)) henergy i
  calc
    cubeLpNorm
        (CubeCalderonZygmund.centralDescendant
          (CubeCalderonZygmund.centralChild Q)
          (oneStepHarmonicGainDepth d hd))
        (oneStepHarmonicExponent d hd).exponent
        (fun x => H.hess i j x) ≤
      oneStepHarmonicGainConstant d hd *
        ∑ k : Fin d,
          cubeLpNorm (CubeCalderonZygmund.centralChild Q) 2
            (fun x => H.hess i k x) := by simpa [P] using hgainHP.2
    _ ≤ oneStepHarmonicGainConstant d hd *
        (3 * A * (cubeScaleFactor Q)⁻¹ *
          ∑ k : Fin d, cubeLpNorm Q 2 (fun x => u.grad x k)) :=
      mul_le_mul_of_nonneg_left hnormalized
        (oneStepHarmonicGainConstant_pos d hd).le
    _ = (3 * oneStepHarmonicGainConstant d hd * A) *
        (cubeScaleFactor Q)⁻¹ *
          ∑ k : Fin d, cubeLpNorm Q 2 (fun x => u.grad x k) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
