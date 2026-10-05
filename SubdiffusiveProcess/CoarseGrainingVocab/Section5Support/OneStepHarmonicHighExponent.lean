module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHarmonicHessianCoordinate

@[expose] public section

/-!
# Fixed high-exponent harmonic Hessian localization

This module assembles the normalized first-child Hessian estimate with the
coordinatewise `L^(16d)` harmonic-gradient gain.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The weak Hessian of a harmonic function has normalized `L^(16d)` control
on a fixed central descendant.  The descendant depth and constant depend only
on `d`; neither depends on the cube or on the harmonic function. -/
theorem exists_harmonic_fixedInterior_hessian_highExponent_bound
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ depth : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
            uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
              ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
                ∀ i j : Fin d,
                  MemLp (fun x => H.hess i j x)
                    (oneStepHarmonicExponent d hd).exponent
                    (normalizedCubeMeasure
                      (CubeCalderonZygmund.centralDescendant
                        (CubeCalderonZygmund.centralChild Q) depth)) ∧
                  cubeLpNorm
                      (CubeCalderonZygmund.centralDescendant
                        (CubeCalderonZygmund.centralChild Q) depth)
                      (oneStepHarmonicExponent d hd).exponent
                      (fun x => H.hess i j x) ≤
                    C * (cubeScaleFactor Q)⁻¹ *
                      ∑ k : Fin d, cubeLpNorm Q 2 (fun x => u.grad x k) := by
  obtain ⟨A, hApos, hA⟩ :=
    exists_harmonic_centralChild_normalized_hessian_bound d
  let C : ℝ := 3 * oneStepHarmonicGainConstant d hd * A
  refine ⟨oneStepHarmonicGainDepth d hd, C, ?_, ?_⟩
  · dsimp [C]
    exact mul_pos
      (mul_pos (by norm_num) (oneStepHarmonicGainConstant_pos d hd)) hApos
  · intro Q u hu
    obtain ⟨uS, huSfun, huSgrad, H, henergy⟩ := hA Q u hu
    refine ⟨uS, huSfun, huSgrad, H, ?_⟩
    intro i j
    have h := harmonic_hessian_coordinate_highExponent_bound hd Q u uS H
      ?_ A henergy i j
    · simpa [C] using h
    · have hsubset : scaledOpenCubeSet Q (1 / 2 : ℝ) ⊆ openCubeSet Q :=
        (scaledOpenCubeSet_subset_scaledClosedCubeSet Q _).trans
          (scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q
            (by norm_num) (by norm_num))
      have hrestrict := hu.restrict
        (isOpen_scaledOpenCubeSet Q _) hsubset
      have huSeq : uS = u.restrict (isOpen_scaledOpenCubeSet Q _) hsubset := by
        apply H1Function.ext
        · simpa [H1Function.restrict] using huSfun
        · simpa [H1Function.restrict] using huSgrad
      rw [huSeq]
      exact hrestrict

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
