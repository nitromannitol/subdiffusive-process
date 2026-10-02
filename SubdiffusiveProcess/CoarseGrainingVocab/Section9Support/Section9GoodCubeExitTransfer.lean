import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTailResidual
import SubdiffusiveProcess.Frozen.Section8.LocalResolventExitUpper




set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-! ## The two objects the transfer needs -/



def GoodCubeSobolevDisplay (a : Vec d → ℝ) (p0 CC : ℝ) (clock : ℝ → ℝ)
    (Q : Cube d) : Prop :=
  ∀ f : H10Function (cubeSet Q),
    lpSq a (cubeSet Q) p0 f.toH1Function.toFun ≤
      ENNReal.ofReal CC * weightedMeasure a (cubeSet Q) ^ (-(1 - 2 / p0)) *
        ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function)

/-- **The continuity route of P-366; the resolution of P363-F3.**  A continuous
killed transition density on `S` for the law `law` and the speed measure
`a dx`. -/
def HasContinuousKilledDensity (a : Vec d → ℝ) (law : Kernel (Vec d) (Path d))
    (S : Set (Vec d)) : Prop :=
  ∃ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law a S p ∧
    ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ S ×ˢ S)

/-! ## Normalisation of the display -/

/-- A finite nonzero extended real is an `ofReal`, and so is every real power
of it. -/
theorem rpow_eq_ofReal_toReal_rpow {x : ENNReal} (hx0 : x ≠ 0) (hxt : x ≠ ⊤)
    (r : ℝ) : x ^ r = ENNReal.ofReal (x.toReal ^ r) := by
  have hpos : 0 < x.toReal := ENNReal.toReal_pos hx0 hxt
  conv_lhs => rw [← ENNReal.ofReal_toReal hxt]
  rw [ENNReal.ofReal_rpow_of_pos hpos]

/-- The good-cube display and the Section 8 hypothesis of
`c.local.resolvent.exit.upper` are the same inequality once the weighted mass
is finite and nonzero. -/
theorem sobolev_display_toReal_form {a : Vec d → ℝ} {p0 CC : ℝ} {clock : ℝ → ℝ}
    {Q : Cube d} (hCC : 0 ≤ CC)
    (hmass0 : weightedMeasure a (cubeSet Q) ≠ 0)
    (hmasstop : weightedMeasure a (cubeSet Q) ≠ ⊤)
    (h : GoodCubeSobolevDisplay a p0 CC clock Q) :
    ∀ f : H10Function (cubeSet Q),
      lpSq a (cubeSet Q) p0 f.toH1Function.toFun ≤
        ENNReal.ofReal (CC *
          ((weightedMeasure a) (cubeSet Q)).toReal ^ (-(1 - 2 / p0)) *
          clock Q.2 * energy a (cubeSet Q) f.toH1Function) := by
  intro f
  refine (h f).trans_eq ?_
  have hnn : (0 : ℝ) ≤ CC *
      ((weightedMeasure a) (cubeSet Q)).toReal ^ (-(1 - 2 / p0)) :=
    mul_nonneg hCC (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  rw [rpow_eq_ofReal_toReal_rpow hmass0 hmasstop, ← ENNReal.ofReal_mul hCC,
    ← ENNReal.ofReal_mul hnn]
  congr 1
  ring

/-! ## The exit-time upper bound on one cube of the family -/

/-- **The upper half of `e.weighted.local.torsion` and of
`e.weighted.local.descendant.torsion`, from the good cube's own Sobolev
display.**  The constant is the one exported by the sealed
`c.local.resolvent.exit.upper`; it depends on `p0` alone. -/
theorem exists_goodCube_exit_upper_constant {p0 : ℝ} (hp0 : 2 < p0) :
    ∃ CE : ℝ, 0 < CE ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ (a : Vec d → ℝ) (law : Kernel (Vec d) (Path d)),
        LocalDiffusion a a law → ∀ (clock : ℝ → ℝ) (A : ℝ), 1 ≤ A →
        ∀ Q : Cube d, 0 < Q.2 → 0 < clock Q.2 →
          weightedMeasure a (cubeSet Q) ≠ 0 →
          weightedMeasure a (cubeSet Q) ≠ ⊤ →
          GoodCubeSobolevDisplay a p0 A clock Q →
          HasContinuousKilledDensity a law (cubeSet Q) →
          ∀ x ∈ cubeSet Q,
            meanExit law (cubeSet Q) x ≤
              ENNReal.ofReal (CE * A ^ CE * clock Q.2) := by
  obtain ⟨c0, CE, hc0, hCE, hmain⟩ :=
    SubdiffusiveProcess.Frozen.Section8.local_resolvent_exit_upper p0 hp0
  refine ⟨CE, hCE, ?_⟩
  intro d hd a law hdiff clock A hA Q hQ hclock hm0 hmt hsob hker
  obtain ⟨p, hp, hpc⟩ := hker
  have hmain' := hmain d hd a a law hdiff (fun i => Q.1 i - Q.2 / 2) Q.2 hQ
    A (clock Q.2) hA hclock
  have hsob' := sobolev_display_toReal_form (le_trans zero_le_one hA) hm0 hmt hsob
  exact fun x hx => ((hmain'.1 (hmain'.2 hsob') p hp hpc).2 x hx)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
