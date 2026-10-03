module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalTorsionSurvival
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpperMean

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ}

/-- The **occupation potential** of `q` on `W`: the expected integral of `q` along the path
until it leaves `W`.  It is the `s → ∞` limit of `s · killedResolvent law W s q`, that is,
the zero-boundary solution of `-∇·(c∇v) = ρ q` in `W`. -/
def occupationPotential (law : Kernel (Vec d) (Path d)) (W : Set (Vec d)) (q : Vec d → ℝ)
    (y : Vec d) : ℝ :=
  ∫ t in Ioi (0 : ℝ),
    ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w},
      q (position (Real.toNNReal t) w) ∂law y

/-- The survival probability is antitone in the time. -/
theorem survival_antitone (law : Kernel (Vec d) (Path d)) (W : Set (Vec d)) (y : Vec d) :
    Antitone (fun t : ℝ => law y {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w}) := by
  intro t₁ t₂ hle
  refine measure_mono fun w hw => ?_
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hle) hw



theorem abs_occupationPotential_le (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {W : Set (Vec d)} (hW : IsOpen W) {q : Vec d → ℝ} {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hqb : ∀ z ∈ W, |q z| ≤ K) {y : Vec d}
    (hy : meanExit law W y ≤ ENNReal.ofReal E) :
    |occupationPotential law W q y| ≤ K * E := by
  classical
  set S : ℝ → Set (Path d) :=
    fun t => {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime W w} with hS
  set g : ℝ → ℝ := fun t => ∫ w in S t, q (position (Real.toNNReal t) w) ∂law y with hg
  set P : ℝ → ℝ := fun t => (law y (S t)).toReal with hP
  -- the survival probability is an integrable antitone function on the half line
  have hsurv_ne : ∀ t : ℝ, law y (S t) ≠ ∞ := fun t => measure_ne_top _ _
  have hPanti : Antitone P := fun t₁ t₂ hle =>
    ENNReal.toReal_mono (hsurv_ne t₁) (survival_antitone law W y hle)
  have hlint : (∫⁻ t in Ioi (0 : ℝ), law y (S t)) = meanExit law W y :=
    (meanExit_eq_lintegral_survival law hW y).symm
  have hlintne : (∫⁻ t in Ioi (0 : ℝ), law y (S t)) ≠ ∞ := by
    rw [hlint]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
  have hPint : IntegrableOn P (Ioi (0 : ℝ)) :=
    integrable_toReal_of_lintegral_ne_top
      ((survival_antitone law W y).measurable.aemeasurable) hlintne
  have hPval : (∫ t in Ioi (0 : ℝ), P t) ≤ E := by
    have hEq : (∫ t in Ioi (0 : ℝ), P t) = (∫⁻ t in Ioi (0 : ℝ), law y (S t)).toReal :=
      integral_toReal ((survival_antitone law W y).measurable.aemeasurable)
        (Eventually.of_forall fun t => lt_of_le_of_ne le_top (hsurv_ne t))
    rw [hEq, hlint]
    calc (meanExit law W y).toReal ≤ (ENNReal.ofReal E).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
      _ = E := ENNReal.toReal_ofReal hE
  -- each inner integral is bounded by `K` times the survival probability
  have hgb : ∀ t ∈ Ioi (0 : ℝ), |g t| ≤ K * P t := by
    intro t ht
    have hmem : ∀ w ∈ S t, |q (position (Real.toNNReal t) w)| ≤ K := by
      intro w hw
      refine hqb _ (localTorsion_position_mem W w (Real.toNNReal t) ?_)
      simpa only [S, Set.mem_setOf_eq, ENNReal.ofReal] using! hw
    have := norm_setIntegral_le_of_norm_le_const (μ := law y) (s := S t)
      (f := fun w => q (position (Real.toNNReal t) w)) (measure_lt_top _ _) hmem
    simpa only [Real.norm_eq_abs, Measure.real, hg, hP] using! this
  have hKP : IntegrableOn (fun t => K * P t) (Ioi (0 : ℝ)) := hPint.const_mul K
  by_cases hgint : IntegrableOn g (Ioi (0 : ℝ))
  · have habs : |∫ t in Ioi (0 : ℝ), g t| ≤ ∫ t in Ioi (0 : ℝ), K * P t := by
      refine le_trans (abs_integral_le_integral_abs) ?_
      refine setIntegral_mono_on hgint.abs hKP measurableSet_Ioi ?_
      exact fun t ht => hgb t ht
    have hfin : (∫ t in Ioi (0 : ℝ), K * P t) ≤ K * E := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hPval hK
    exact le_trans habs hfin
  · rw [occupationPotential, integral_undef hgint]
    simpa using! mul_nonneg hK hE

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
