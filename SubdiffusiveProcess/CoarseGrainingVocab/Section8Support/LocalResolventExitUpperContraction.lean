module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationDensity

@[expose] public section

/-!
# The spectral-gap contraction of the killed resolvent

The Poincaré assumption  is the quadratic form
inequality `‖f‖²_{L²(U,μ)} ≤ A F ℰ(f,f)` on `H¹₀(U)`.  Testing the massive weak equation
supplied by `LocalDiffusion` against its own solution turns it into the resolvent contraction

  `‖R_s^U f‖_{L²(μ)} ≤ (1 + s/(AF))⁻¹ ‖f‖_{L²(μ)}`,

which is the quantitative form of `‖P_t^U‖_{2→2} ≤ e^{-t/(AF)}` used in the manuscript proof.  Iterating the single-step estimate gives the decay of a
finite resolvent power, which is what the exponential mixture comparison consumes.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper

variable {d : ℕ}

/-! ### The exponent-two seminorm as a square root -/

/-- The `L²` seminorm is the square root of the integral of the square. -/
theorem eLpNorm_two_eq_ofReal_sqrt {α : Type*} [MeasurableSpace α] {mu : Measure α}
    {g : α → ℝ} (hg : MemLp g 2 mu) :
    eLpNorm g 2 mu = ENNReal.ofReal (Real.sqrt (∫ x, g x * g x ∂mu)) := by
  have hint : Integrable (fun x => g x * g x) mu := by
    simpa only [Pi.mul_apply] using! hg.integrable_mul hg
  have hnn : (0 : ℝ) ≤ ∫ x, g x * g x ∂mu :=
    integral_nonneg fun x => mul_self_nonneg _
  have he : ∀ x : α, ‖g x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (g x * g x) := by
    intro x
    rw [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    congr 1
    simp [Real.norm_eq_abs, pow_two]
  have hbase := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := mu) (p := (2 : ℝ≥0))
    (by norm_num) hg.aestronglyMeasurable
  have hlint : (∫⁻ x, ENNReal.ofReal (g x * g x) ∂mu)
      = ENNReal.ofReal (∫ x, g x * g x ∂mu) :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => mul_self_nonneg _)).symm
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at hbase
  have hsq : eLpNorm g 2 mu ^ (2 : ℝ) = ENNReal.ofReal (∫ x, g x * g x ∂mu) := by
    calc eLpNorm g 2 mu ^ (2 : ℝ) = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂mu := hbase
      _ = ∫⁻ x, ENNReal.ofReal (g x * g x) ∂mu := lintegral_congr fun x => he x
      _ = ENNReal.ofReal (∫ x, g x * g x ∂mu) := hlint
  have hrhs : (ENNReal.ofReal (Real.sqrt (∫ x, g x * g x ∂mu))) ^ (2 : ℝ)
      = ENNReal.ofReal (∫ x, g x * g x ∂mu) := by
    rw [ENNReal.rpow_two, pow_two, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      Real.mul_self_sqrt hnn]
  exact ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0) (hsq.trans hrhs.symm)

/-! ### Testing the massive equation against its own solution -/

/-- Testing the normalized massive equation with its own solution gives the mass plus `s` times
the energy. -/
theorem mass_add_energy_eq {U : Set (Vec d)} {c rho f : Vec d → ℝ} {s : ℝ} (hs : 0 < s)
    {u : H10Function U}
    (hu : IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function (fun x => s⁻¹ * f x)) :
    (∫ x in U, rho x * u.toH1Function.toFun x * u.toH1Function.toFun x) +
        s * energy c U u.toH1Function =
      ∫ x in U, rho x * f x * u.toH1Function.toFun x := by
  have heq := hu u
  have henergy : (∫ x in U, vecDot (c x • u.toH1Function.grad x) (u.toH1Function.grad x))
      = energy c U u.toH1Function :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simpa using! vecDot_smul_left (c x) (u.toH1Function.grad x) (u.toH1Function.grad x))
  rw [henergy] at heq
  have hscaled : (∫ x in U, rho x * (s⁻¹ * f x) * u.toH1Function.toFun x) =
      s⁻¹ * ∫ x in U, rho x * f x * u.toH1Function.toFun x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hscaled] at heq
  have heq' := congrArg (fun z : ℝ => s * z) heq
  simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at heq'
  linarith

/-! ### The single-step contraction -/

/-- Cauchy--Schwarz for the weighted pairing, in the seminorm normalization. -/
theorem abs_integral_mul_le_toReal_mul {α : Type*} [MeasurableSpace α] {mu : Measure α}
    {g h : α → ℝ} (hg : MemLp g 2 mu) (hh : MemLp h 2 mu) :
    |∫ x, g x * h x ∂mu| ≤ (eLpNorm g 2 mu).toReal * (eLpNorm h 2 mu).toReal := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hprod : (∫⁻ x, ‖g x‖ₑ * ‖h x‖ₑ ∂mu) ≤ eLpNorm g 2 mu * eLpNorm h 2 mu := by
    have hbase := ENNReal.lintegral_mul_le_Lp_mul_Lq mu hpq
      hg.aestronglyMeasurable.enorm hh.aestronglyMeasurable.enorm
    have hgb := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := mu) (p := (2 : ℝ≥0))
      (by norm_num) hg.aestronglyMeasurable
    have hhb := eLpNorm_nnreal_pow_eq_lintegral (f := h) (μ := mu) (p := (2 : ℝ≥0))
      (by norm_num) hh.aestronglyMeasurable
    simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at hgb hhb
    have hg2 : (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) = eLpNorm g 2 mu := by
      rw [← hgb, ← ENNReal.rpow_mul]
      norm_num
    have hh2 : (∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) = eLpNorm h 2 mu := by
      rw [← hhb, ← ENNReal.rpow_mul]
      norm_num
    calc (∫⁻ x, ‖g x‖ₑ * ‖h x‖ₑ ∂mu)
        ≤ (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) *
            (∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
          simpa only [Pi.mul_apply] using! hbase
      _ = eLpNorm g 2 mu * eLpNorm h 2 mu := by rw [hg2, hh2]
  have hfin : eLpNorm g 2 mu * eLpNorm h 2 mu ≠ ∞ :=
    ENNReal.mul_ne_top hg.eLpNorm_ne_top hh.eLpNorm_ne_top
  have habs : ‖∫ x, g x * h x ∂mu‖ₑ ≤ eLpNorm g 2 mu * eLpNorm h 2 mu := by
    refine le_trans (enorm_integral_le_lintegral_enorm _) (le_trans (le_of_eq ?_) hprod)
    exact lintegral_congr fun x => by rw [enorm_mul]
  have := ENNReal.toReal_mono hfin habs
  rwa [ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] at this

/-- **The spectral-gap contraction of the killed resolvent.**  Under the Poincaré assumption the
killed resolvent contracts the weighted `L²` seminorm by `(1 + s/(AF))⁻¹`. -/
theorem eLpNorm_two_killedResolvent_le {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {A F s : ℝ} (hA : 0 < A) (hF : 0 < F) (hs : 0 < s)
    (hPoin : PoincareAssumption c rho U A F)
    {f : Vec d → ℝ} (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) :
    eLpNorm (killedResolvent law U s f) 2 ((weightedMeasure rho).restrict U) ≤
      ENNReal.ofReal ((1 + s / (A * F))⁻¹) *
        eLpNorm f 2 ((weightedMeasure rho).restrict U) := by
  set mu := (weightedMeasure rho).restrict U with hmu
  have hr : CoefficientOn U rho :=
    coefficientOn_mono subset_closure (hD.2.1 (closure U) hUb.isCompact_closure).2
  obtain ⟨u, hueq, hsol⟩ := hD.2.2 U hU hUb s hs f hf
  set v : Vec d → ℝ := u.toH1Function.toFun with hv
  have humem : MemLp v 2 mu :=
    memLp_weighted_of_volume_restrict hU.measurableSet hr u.toH1Function.memL2
  set M : ℝ := ∫ x, v x * v x ∂mu with hM
  set E : ℝ := energy c U u.toH1Function with hE
  have hM0 : 0 ≤ M := integral_nonneg fun x => mul_self_nonneg _
  -- the tested equation, in the weighted measure
  have hmassU : (∫ x in U, rho x * v x * v x) = M := by
    rw [hM, integral_weightedMeasure_restrict_eq hU.measurableSet rho (fun x => v x * v x) hr]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hmassF : (∫ x in U, rho x * f x * v x) = ∫ x, f x * v x ∂mu := by
    rw [integral_weightedMeasure_restrict_eq hU.measurableSet rho (fun x => f x * v x) hr]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have htest : M + s * E = ∫ x, f x * v x ∂mu := by
    have := mass_add_energy_eq hs hsol
    rw [hmassU, hmassF] at this
    exact this
  -- the Poincaré assumption in the same normalization
  have hpoin : ENNReal.ofReal M ≤ ENNReal.ofReal (A * F * E) := by
    have hlp := hPoin u
    rw [lpSq_two_eq_lintegral] at hlp
    have hint : Integrable (fun x => v x * v x) mu := by
      simpa only [Pi.mul_apply] using! humem.integrable_mul humem
    have hlint : (∫⁻ x, ENNReal.ofReal (v x * v x) ∂mu) = ENNReal.ofReal M :=
      (ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun x => mul_self_nonneg _)).symm
    rwa [hlint] at hlp
  -- Cauchy--Schwarz on the right-hand side
  have hCS : |∫ x, f x * v x ∂mu| ≤ (eLpNorm f 2 mu).toReal * (eLpNorm v 2 mu).toReal :=
    abs_integral_mul_le_toReal_mul hf humem
  set nf : ℝ := (eLpNorm f 2 mu).toReal with hnf
  set nu : ℝ := (eLpNorm v 2 mu).toReal with hnu
  have hnf0 : 0 ≤ nf := ENNReal.toReal_nonneg
  have hnu0 : 0 ≤ nu := ENNReal.toReal_nonneg
  have hnusq : nu * nu = M := by
    rw [hnu, eLpNorm_two_eq_ofReal_sqrt humem, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      Real.mul_self_sqrt hM0]
  -- the gap inequality
  have hkey : nu * (1 + s / (A * F)) ≤ nf := by
    rcases le_or_gt 0 (A * F * E) with hAFE | hAFE
    · have hMle : M ≤ A * F * E := (ENNReal.ofReal_le_ofReal_iff hAFE).mp hpoin
      have hAF : 0 < A * F := mul_pos hA hF
      have hE0 : 0 ≤ E := by
        by_contra hcon
        push Not at hcon
        nlinarith [mul_pos hAF (neg_pos.mpr hcon)]
      have hEge : M / (A * F) ≤ E := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have hchain : M + s * (M / (A * F)) ≤ nf * nu := by
        have h1 : M + s * (M / (A * F)) ≤ M + s * E := by nlinarith
        have h2 : ∫ x, f x * v x ∂mu ≤ nf * nu := le_trans (le_abs_self _) hCS
        have h3 : M + s * E ≤ nf * nu := by rw [htest]; exact h2
        linarith
      rcases eq_or_lt_of_le hnu0 with hnu0' | hnupos
      · have hM0' : M = 0 := by rw [← hnusq, ← hnu0']; ring
        rw [← hnu0']
        simpa using! hnf0
      · have hMpos : 0 < M := by nlinarith
        have hexp : M + s * (M / (A * F)) = M * (1 + s / (A * F)) := by
          field_simp
        rw [hexp] at hchain
        have : nu * nu * (1 + s / (A * F)) ≤ nf * nu := by rw [hnusq]; exact hchain
        nlinarith
    · have hzero : ENNReal.ofReal (A * F * E) = 0 :=
        ENNReal.ofReal_eq_zero.mpr (le_of_lt hAFE)
      have hM0' : M = 0 := by
        have : ENNReal.ofReal M = 0 := le_antisymm (hzero ▸ hpoin) zero_le
        have := ENNReal.ofReal_eq_zero.mp this
        linarith
      have hnu0' : nu = 0 := by nlinarith [hnusq]
      rw [hnu0']
      simpa using! hnf0
  -- conclude
  have hpos : 0 < 1 + s / (A * F) := by positivity
  have hnule : nu ≤ (1 + s / (A * F))⁻¹ * nf := by
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    exact hkey
  have hres : eLpNorm (killedResolvent law U s f) 2 mu = eLpNorm v 2 mu :=
    eLpNorm_congr_ae (Filter.EventuallyEq.symm hueq)
  rw [hres]
  have hvfin : eLpNorm v 2 mu ≠ ∞ := humem.eLpNorm_ne_top
  have hffin : eLpNorm f 2 mu ≠ ∞ := hf.eLpNorm_ne_top
  calc eLpNorm v 2 mu = ENNReal.ofReal nu := by
        rw [hnu, ENNReal.ofReal_toReal hvfin]
    _ ≤ ENNReal.ofReal ((1 + s / (A * F))⁻¹ * nf) := ENNReal.ofReal_le_ofReal hnule
    _ = ENNReal.ofReal ((1 + s / (A * F))⁻¹) * ENNReal.ofReal nf :=
        ENNReal.ofReal_mul (by positivity)
    _ = ENNReal.ofReal ((1 + s / (A * F))⁻¹) * eLpNorm f 2 mu := by
        rw [hnf, ENNReal.ofReal_toReal hffin]

/-- The iterated killed resolvent contracts by the same factor at every step. -/
theorem eLpNorm_two_iterate_killedResolvent_le {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {A F s : ℝ} (hA : 0 < A) (hF : 0 < F) (hs : 0 < s)
    (hPoin : PoincareAssumption c rho U A F)
    {f : Vec d → ℝ} (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) (n : ℕ) :
    MemLp ((killedResolvent law U s)^[n] f) 2 ((weightedMeasure rho).restrict U) ∧
      eLpNorm ((killedResolvent law U s)^[n] f) 2 ((weightedMeasure rho).restrict U) ≤
        ENNReal.ofReal ((1 + s / (A * F))⁻¹) ^ n *
          eLpNorm f 2 ((weightedMeasure rho).restrict U) := by
  induction n with
  | zero => simpa using! hf
  | succ n ih =>
    obtain ⟨hmem, hbound⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply']
      exact memLp_killedResolvent hD hU hUb hs hmem
    · rw [Function.iterate_succ_apply']
      calc eLpNorm (killedResolvent law U s ((killedResolvent law U s)^[n] f)) 2
            ((weightedMeasure rho).restrict U)
          ≤ ENNReal.ofReal ((1 + s / (A * F))⁻¹) *
              eLpNorm ((killedResolvent law U s)^[n] f) 2 ((weightedMeasure rho).restrict U) :=
            eLpNorm_two_killedResolvent_le hD hU hUb hA hF hs hPoin hmem
        _ ≤ ENNReal.ofReal ((1 + s / (A * F))⁻¹) *
              (ENNReal.ofReal ((1 + s / (A * F))⁻¹) ^ n *
                eLpNorm f 2 ((weightedMeasure rho).restrict U)) := by
            gcongr
        _ = ENNReal.ofReal ((1 + s / (A * F))⁻¹) ^ (n + 1) *
              eLpNorm f 2 ((weightedMeasure rho).restrict U) := by
            rw [pow_succ]
            ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
