module

public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientGainIteration

@[expose] public section

/-!
# The fixed high-exponent harmonic-gain carrier for the one-step proof

This small module chooses the library's finite-exponent harmonic-gradient
carrier once.  Keeping the choice behind an ordinary compiled definition
prevents downstream localization proofs from repeatedly reducing the full
Sobolev-ladder construction.
-/

open Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The exponent `16d` leaves only one sixteenth of the descendant-volume
loss when an `L^(16d)` Hessian is restricted to a smaller cell. -/
noncomputable def oneStepHarmonicExponent (d : ℕ) (hd : 3 ≤ d) :
    FiniteLpExponent where
  exponent := ENNReal.ofReal (16 * (d : ℝ))
  one_lt := by
    rw [ENNReal.one_lt_ofReal]
    have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  lt_top := ENNReal.ofReal_lt_top

@[simp] theorem oneStepHarmonicExponent_toReal (d : ℕ) (hd : 3 ≤ d) :
    (oneStepHarmonicExponent d hd).exponent.toReal = 16 * (d : ℝ) := by
  simp [oneStepHarmonicExponent]

/-- The dimension-only depth and harmonic-gradient gain at exponent `16d`. -/
noncomputable def oneStepHarmonicGainPacked (d : ℕ) (hd : 3 ≤ d) :
    Σ depth : ℕ,
      CubeCalderonZygmund.INTERNAL.HarmonicGradientGain d
        (oneStepHarmonicExponent d hd) depth :=
  Classical.choice
    (CubeCalderonZygmund.INTERNAL.nonempty_harmonicGradientGain_finiteTarget_of_three_le
      d hd (oneStepHarmonicExponent d hd))

/-- The fixed interior depth selected by `oneStepHarmonicGainPacked`. -/
noncomputable def oneStepHarmonicGainDepth (d : ℕ) (hd : 3 ≤ d) : ℕ :=
  (oneStepHarmonicGainPacked d hd).1

/-- The selected normalized `L^(16d)` harmonic-gradient gain. -/
noncomputable def oneStepHarmonicGain (d : ℕ) (hd : 3 ≤ d) :
    CubeCalderonZygmund.INTERNAL.HarmonicGradientGain d
      (oneStepHarmonicExponent d hd) (oneStepHarmonicGainDepth d hd) :=
  (oneStepHarmonicGainPacked d hd).2

/-- The finite positive constant of the selected gain, as a real number. -/
noncomputable def oneStepHarmonicGainConstant (d : ℕ) (hd : 3 ≤ d) : ℝ :=
  (oneStepHarmonicGain d hd).constant.toReal

theorem oneStepHarmonicGainConstant_pos (d : ℕ) (hd : 3 ≤ d) :
    0 < oneStepHarmonicGainConstant d hd := by
  exact ENNReal.toReal_pos
    (ne_of_gt (oneStepHarmonicGain d hd).constant_pos)
    (oneStepHarmonicGain d hd).constant_ne_top

/-- Membership endpoint of the selected harmonic gain. -/
theorem oneStepHarmonicGain_memLp (d : ℕ) (hd : 3 ≤ d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (h : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0)) (i : Fin d) :
    MeasureTheory.MemLp (fun x => u.grad x i)
      (oneStepHarmonicExponent d hd).exponent
      (normalizedCubeMeasure
        (CubeCalderonZygmund.centralDescendant Q
          (oneStepHarmonicGainDepth d hd))) :=
  (oneStepHarmonicGain d hd).memLp Q u h i

/-- Norm endpoint of the selected harmonic gain. -/
theorem oneStepHarmonicGain_bound (d : ℕ) (hd : 3 ≤ d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (h : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0)) (i : Fin d) :
    MeasureTheory.eLpNorm (fun x => u.grad x i)
        (oneStepHarmonicExponent d hd).exponent
        (normalizedCubeMeasure
          (CubeCalderonZygmund.centralDescendant Q
            (oneStepHarmonicGainDepth d hd))) ≤
      ENNReal.ofReal (oneStepHarmonicGainConstant d hd) *
        ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2
            (normalizedCubeMeasure Q) := by
  have h := (oneStepHarmonicGain d hd).bound Q u h i
  have hconst :
      ENNReal.ofReal (oneStepHarmonicGainConstant d hd) =
        (oneStepHarmonicGain d hd).constant := by
    rw [oneStepHarmonicGainConstant, ENNReal.ofReal_toReal]
    exact (oneStepHarmonicGain d hd).constant_ne_top
  simpa [hconst] using h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
