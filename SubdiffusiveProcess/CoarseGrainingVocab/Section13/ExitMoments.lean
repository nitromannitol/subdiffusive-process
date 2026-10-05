module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

/-!
# Exit-time moments

Section 13 states its exit-time conclusions in terms of `E_x[τ_{B_R(x)}^q]` for every
`q > 0`, whereas the tree so far carries only the first moment
(`SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.meanExit`). This file adds the `q`-th
moment and records that it specializes to `meanExit` at `q = 1`.

Source: `lim:cor-paths` and `lim:cor-exit-moments` (`c.diffusion.exit.displacement`),
`lim:cor-paths` and `lim:cor-exit-moments` (`c.diffusion.power.laws`), `lim:cor-paths` and `lim:cor-exit-moments`
(`c.diffusion.exit.time.comparison`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MarkovProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section13

variable {d : ℕ}

/-- `E_x[τ_U^q]`, the `q`-th moment of the exit time of `U`. -/
def exitMoment (law : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (q : ℝ)
    (x : Vec d) : ENNReal :=
  ∫⁻ w, (LifetimePath.exitTime U w) ^ q ∂law x

@[simp] theorem exitMoment_one (law : Kernel (Vec d) (Path d)) (U : Set (Vec d))
    (x : Vec d) : exitMoment law U 1 x = meanExit law U x := by
  unfold exitMoment meanExit
  refine lintegral_congr fun w => ?_
  simp

/-- The exit moment is monotone in the domain, because the exit time is. -/
theorem exitMoment_mono_of_exitTime_le {law : Kernel (Vec d) (Path d)}
    {U V : Set (Vec d)} {q : ℝ} (hq : 0 ≤ q) (x : Vec d)
    (h : ∀ w, LifetimePath.exitTime U w ≤ LifetimePath.exitTime V w) :
    exitMoment law U q x ≤ exitMoment law V q x := by
  unfold exitMoment
  exact lintegral_mono fun w => ENNReal.rpow_le_rpow (h w) hq

/-- Monotone in the exponent on a domain whose exit time is at least one. -/
theorem exitMoment_mono_exponent {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}
    {q r : ℝ} (hqr : q ≤ r) (x : Vec d)
    (hone : ∀ w, 1 ≤ LifetimePath.exitTime U w) :
    exitMoment law U q x ≤ exitMoment law U r x := by
  unfold exitMoment
  exact lintegral_mono fun w => ENNReal.rpow_le_rpow_of_exponent_le (hone w) hqr

end SubdiffusiveProcess.CoarseGrainingVocab.Section13
