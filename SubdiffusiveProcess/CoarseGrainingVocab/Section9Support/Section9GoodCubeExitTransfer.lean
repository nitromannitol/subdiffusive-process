module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTailResidual
public import SubdiffusiveProcess.Section8.LocalResolventExitUpper

@[expose] public section

/-!
# From the good cube's Sobolev display to the exit-time upper bounds


(the upper halves of the weighted local torsion estimate and of its descendant version).

The residual displays `exit_upper` and the upper half of `descendant` of
`GoodCubeResidualDisplays` are **not** independent estimates: they are
the `SubdiffusiveProcess.Section8.local_resolvent_exit_upper` applied to the
residual's own `sobolev` display.  This file performs that application once,
for one cube of the local family, and records the two side conditions it needs.

* `GoodCubeSobolevDisplay` is the residual's `sobolev` field read on a single
  cube.  `sobolev_display_toReal_form` turns it into the Section 8 shape, which
  the lemma's own second conjunct converts into the standing
  `SobolevAssumption`/`PoincareAssumption` pair.  The conversion is the
  elementary one between `ENNReal.rpow` of the weighted mass and the real power
  of its `toReal`; it needs the mass to be neither zero nor infinite, which is
  supplied on the good event by the two-sided ellipticity of P373-F2.

* `HasContinuousKilledDensity` is the **continuity route** of and the
  resolution of **P363-F3**.  `LocalDiffusion` identifies the resolvent with
  the massive weak solution only `∀ᵐ x ∂(weightedMeasure rho).restrict U`, so a
  law modified at a single starting point still satisfies it and can have an
  infinite mean exit time there, while every exit display of the good-cube
  package is pointwise in the starting point.  A killed density pins `law x` at
  **every** `x ∈ U` — its defining identity in `IsKilledDensity` is quantified
  pointwise — so the qualification disappears on the class of laws carrying
  one.  This is exactly the hypothesis that the
  `SubdiffusiveProcess.Section8.local_resolvent_exit_upper` and the
  `SubdiffusiveProcess.Section9.weighted_local_killed_kernel` already
  carry, so nothing new is introduced by asking for it here.
-/

set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-! ## The two objects the transfer needs -/

/-- The `sobolev` field of `GoodCubeResidualDisplays`, read on a single cube of
the local family. -/
def GoodCubeSobolevDisplay (a : Vec d → ℝ) (p0 CC : ℝ) (clock : ℝ → ℝ)
    (Q : Cube d) : Prop :=
  ∀ f : H10Function (cubeSet Q),
    lpSq a (cubeSet Q) p0 f.toH1Function.toFun ≤
      ENNReal.ofReal CC * weightedMeasure a (cubeSet Q) ^ (-(1 - 2 / p0)) *
        ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function)

/-- **The continuity route.**  A continuous
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
the local-resolvent exit-time estimate are the same inequality once the weighted mass
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

/-- **The upper half of the weighted local torsion estimate and of its descendant version, from the
good cube's own Sobolev display.** The constant is the one exported by the
`SubdiffusiveProcess.Section8.local_resolvent_exit_upper`; it depends on `p0` alone. -/
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
    _root_.SubdiffusiveProcess.Section8.local_resolvent_exit_upper p0 hp0
  refine ⟨CE, hCE, ?_⟩
  intro d hd a law hdiff clock A hA Q hQ hclock hm0 hmt hsob hker
  obtain ⟨p, hp, hpc⟩ := hker
  have hmain' := hmain d hd a a law hdiff (fun i => Q.1 i - Q.2 / 2) Q.2 hQ
    A (clock Q.2) hA hclock
  have hsob' := sobolev_display_toReal_form (le_trans zero_le_one hA) hm0 hmt hsob
  exact fun x hx => ((hmain'.1 (hmain'.2 hsob') p hp hpc).2 x hx)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
