module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5RobustSobolevDisplay

@[expose] public section




set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

theorem aestronglyMeasurable_weightedMeasure_restrict {a : Vec d → ℝ} {U : Set (Vec d)}
    (f : H10Function U) :
    AEStronglyMeasurable f.toH1Function.toFun ((weightedMeasure a).restrict U) :=
  f.toH1Function.memL2.aestronglyMeasurable.mono_ac
    ((withDensity_absolutelyContinuous volume fun x => ENNReal.ofReal (a x)).restrict U)

theorem lpSq_two_le_lpSq_mul_rpow {a : Vec d → ℝ} {U : Set (Vec d)} {p0 : ℝ}
    (hp0 : 2 < p0) (f : H10Function U) :
    lpSq a U 2 f.toH1Function.toFun ≤
      lpSq a U p0 f.toH1Function.toFun * weightedMeasure a U ^ (1 - 2 / p0) := by
  have hp0pos : (0:ℝ) < p0 := by linarith
  have hle : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p0 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hmeas := aestronglyMeasurable_weightedMeasure_restrict (a := a) f
  have hraw (q : ℝ≥0∞) :
      SubdiffusiveProcess.RawLp.eLpNorm f.toFun q
        ((volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict U) =
      eLpNorm f.toFun q ((weightedMeasure a).restrict U) := by
    simpa only [weightedMeasure] using! SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (p := q) hmeas
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (2 : ℝ≥0∞))
    (q := ENNReal.ofReal p0) hle hmeas
  have huniv : ((weightedMeasure a).restrict U) Set.univ = weightedMeasure a U := by
    rw [Measure.restrict_apply_univ]
  have htr : (1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p0).toReal) = 1 / 2 - 1 / p0 := by
    rw [ENNReal.toReal_ofReal hp0pos.le]
    norm_num
  rw [huniv, htr] at h
  have hsq := pow_le_pow_left' h 2
  calc lpSq a U 2 f.toH1Function.toFun
      = (eLpNorm f.toH1Function.toFun 2 ((weightedMeasure a).restrict U)) ^ (2:ℕ) := by
        rw [lpSq, hraw]
        congr 2
        simp
    _ ≤ (eLpNorm f.toH1Function.toFun (ENNReal.ofReal p0)
          ((weightedMeasure a).restrict U) * weightedMeasure a U ^ (1/2 - 1/p0)) ^ (2:ℕ) := hsq
    _ = lpSq a U p0 f.toH1Function.toFun * weightedMeasure a U ^ (1 - 2 / p0) := by
        rw [mul_pow, lpSq, hraw, ← ENNReal.rpow_natCast (weightedMeasure a U ^ (1/2 - 1/p0)) 2,
          ← ENNReal.rpow_mul]
        congr 2
        push_cast
        ring

/-- **The weighted Poincare inequality is already inside the Sobolev field.** -/
theorem poincareAssumption_of_goodCubeSobolevDisplay {a : Vec d → ℝ} {p0 CC : ℝ}
    {clock : ℝ → ℝ} {Q : Cube d} (hp0 : 2 < p0) (hCC : 0 ≤ CC)
    (hW0 : weightedMeasure a (cubeSet Q) ≠ 0)
    (hWtop : weightedMeasure a (cubeSet Q) ≠ ⊤)
    (h : GoodCubeSobolevDisplay a p0 CC clock Q) :
    PoincareAssumption a a (cubeSet Q) CC (clock Q.2) := by
  intro f
  set W : ℝ≥0∞ := weightedMeasure a (cubeSet Q) with hW
  have hstep := lpSq_two_le_lpSq_mul_rpow (a := a) (U := cubeSet Q) hp0 f
  have hdisp := h f
  have hmul : lpSq a (cubeSet Q) p0 f.toH1Function.toFun * W ^ (1 - 2 / p0) ≤
      (ENNReal.ofReal CC * W ^ (-(1 - 2 / p0)) *
        ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function)) *
        W ^ (1 - 2 / p0) := mul_le_mul_left hdisp _
  have hcancel : (ENNReal.ofReal CC * W ^ (-(1 - 2 / p0)) *
        ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function)) * W ^ (1 - 2 / p0)
      = ENNReal.ofReal (CC * (clock Q.2 * energy a (cubeSet Q) f.toH1Function)) := by
    rw [ENNReal.ofReal_mul hCC]
    rw [show ENNReal.ofReal CC * W ^ (-(1 - 2 / p0)) *
        ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function) * W ^ (1 - 2 / p0)
      = ENNReal.ofReal CC * ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function) *
        (W ^ (-(1 - 2 / p0)) * W ^ (1 - 2 / p0)) by ring]
    rw [← ENNReal.rpow_add _ _ hW0 hWtop]
    simp
  have hfinal := hstep.trans (hmul.trans (le_of_eq hcancel))
  refine hfinal.trans (le_of_eq ?_)
  congr 1
  ring

/-- **The robust weighted Poincare inequality.**  Composing Step S with the Holder step: the
multiplied coefficient satisfies the weighted Poincare inequality on the cube with the same
`(1+eps)/(1-eps)` loss, and again with no dependence on the multiplier's scale. -/
theorem poincareAssumption_mul_of_admissible {S : Set (Vec d)} {Q : Cube d}
    (hQm : MeasurableSet (cubeSet Q)) (hQS : cubeSet Q ⊆ S)
    {a theta : Vec d → ℝ} {p0 CC epsilon : ℝ} {clock : ℝ → ℝ}
    (hp0 : 2 < p0) (hCC : 0 ≤ CC) (hclock : 0 ≤ clock Q.2)
    (heps0 : 0 ≤ epsilon) (heps1 : epsilon < 1)
    (ha : ∀ x ∈ S, 0 ≤ a x)
    (hadm : GoodCubeV5AdmissibleMultiplier S epsilon theta)
    (hW0 : weightedMeasure a (cubeSet Q) ≠ 0)
    (hWfin : weightedMeasure a (cubeSet Q) ≠ ⊤)
    (hint1 : ∀ f : H10Function (cubeSet Q), IntegrableOn
      (fun x => a x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x)) (cubeSet Q))
    (hint2 : ∀ f : H10Function (cubeSet Q), IntegrableOn
      (fun x => a x * theta x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
      (cubeSet Q))
    (hdisp : GoodCubeSobolevDisplay a p0 CC clock Q) :
    PoincareAssumption (fun x => a x * theta x) (fun x => a x * theta x) (cubeSet Q)
      (CC * (1 + epsilon) / (1 - epsilon)) (clock Q.2) := by
  obtain ⟨k, hk, hkb⟩ := admissibleMultiplier_bounds hadm
  have hu : 0 < k * (1 + epsilon) := by nlinarith
  have hl : 0 < k * (1 - epsilon) := by nlinarith
  have hlow : ENNReal.ofReal (k * (1 - epsilon)) * weightedMeasure a (cubeSet Q) ≤
      weightedMeasure (fun x => a x * theta x) (cubeSet Q) :=
    le_weightedMeasure_mul hQm hQS hl.le ha (fun x hx => (hkb x hx).1)
  have hhigh : weightedMeasure (fun x => a x * theta x) (cubeSet Q) ≤
      ENNReal.ofReal (k * (1 + epsilon)) * weightedMeasure a (cubeSet Q) :=
    weightedMeasure_mul_le hQm hQS hu.le ha (fun x hx => (hkb x hx).2)
  have hW0' : weightedMeasure (fun x => a x * theta x) (cubeSet Q) ≠ 0 := by
    intro hzero
    rw [hzero, le_zero_iff, mul_eq_zero] at hlow
    rcases hlow with h | h
    · exact absurd h (by simpa using hl)
    · exact hW0 h
  have hWtop' : weightedMeasure (fun x => a x * theta x) (cubeSet Q) ≠ ⊤ := by
    intro htop
    rw [htop, top_le_iff, ENNReal.mul_eq_top] at hhigh
    rcases hhigh with ⟨-, h⟩ | ⟨h, -⟩
    · exact hWfin h
    · exact absurd h ENNReal.ofReal_ne_top
  have hCC' : 0 ≤ CC * (1 + epsilon) / (1 - epsilon) := by
    have : (0:ℝ) < 1 - epsilon := by linarith
    positivity
  exact poincareAssumption_of_goodCubeSobolevDisplay hp0 hCC' hW0' hWtop'
    (goodCubeSobolevDisplay_mul_of_admissible hQm hQS hp0 hCC hclock heps0 heps1 ha hadm
      hWfin hint1 hint2 hdisp)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
