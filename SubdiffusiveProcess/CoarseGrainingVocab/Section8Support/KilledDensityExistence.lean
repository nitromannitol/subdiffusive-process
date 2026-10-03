module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationDensity

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}



def KilledLawAbsolutelyContinuousOn (law : Kernel (Vec d) (Path d)) (rho : Vec d → ℝ)
    (U : Set (Vec d)) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x ∈ U, ∀ B : Set (Vec d), MeasurableSet B →
    (weightedMeasure rho) (B ∩ U) = 0 →
      law x {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
        LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} = 0




/-! ## Finiteness of the weighted mass of a bounded domain -/

/-- A bounded domain carrying an elliptic weight has finite weighted mass. -/
theorem weightedMeasure_ne_top (hrho : CoefficientOn U rho) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) : (weightedMeasure rho) U ≠ ∞ := by
  obtain ⟨-, lo, hi, -, hbd⟩ := hrho
  have hle : (weightedMeasure rho) U ≤ ENNReal.ofReal hi * volume U := by
    rw [weightedMeasure, withDensity_apply _ hU.measurableSet]
    calc
      (∫⁻ x in U, ENNReal.ofReal (rho x)) ≤ ∫⁻ _x in U, ENNReal.ofReal hi :=
        lintegral_mono_ae (hbd.mono fun x hx => ENNReal.ofReal_le_ofReal hx.2)
      _ = ENNReal.ofReal hi * volume U := by
        rw [lintegral_const, Measure.restrict_apply_univ]
  exact (hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUb.measure_lt_top)).ne

/-- The weighted measure of a bounded domain of a local diffusion is finite. -/
theorem weightedMeasure_ne_top_of_localDiffusion (hD : LocalDiffusion c rho law)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) : (weightedMeasure rho) U ≠ ∞ :=
  weightedMeasure_ne_top
    (coefficientOn_mono subset_closure (hD.2.1 (closure U) hUb.isCompact_closure).2) hU hUb

/-- The restriction of a weighted measure of finite mass is a finite measure. -/
theorem isFiniteMeasure_restrict (hfin : (weightedMeasure rho) U ≠ ∞) :
    IsFiniteMeasure ((weightedMeasure rho).restrict U) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact lt_of_le_of_ne le_top hfin

/-! ## The killed kernel and the killed law -/

/-- The killed kernel at a real time is the killed law of the frozen
`IsKilledDensity` event. -/
theorem killedKernel_apply_law (law : Kernel (Vec d) (Path d)) {U : Set (Vec d)}
    (hU : IsOpen U) (t : ℝ) (x : Vec d) (B : Set (Vec d)) (hB : MeasurableSet B) :
    killedKernel law U hU (Real.toNNReal t) x B
      = law x {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
        LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} := by
  rw [killed_apply law U hU _ x B hB]
  congr 1
  ext w
  constructor
  · rintro ⟨hmem, hlt⟩
    obtain ⟨z, -, hcoord⟩ :=
      LifetimePath.exists_coordinate_eq_alive_of_lt_exitTime U w (Real.toNNReal t) hlt
    refine ⟨hlt, ?_⟩
    rw [hcoord]
    exact ⟨z, by rwa [← position_of_alive (Real.toNNReal t) w z hcoord], rfl⟩
  · rintro ⟨hlt, ⟨z, hzB, hz⟩⟩
    exact ⟨by rw [position_of_alive (Real.toNNReal t) w z hz.symm]; exact hzB, hlt⟩

/-! ## What `LocalDiffusion` already gives: the almost-everywhere condition -/

/-- **Almost every starting point already satisfies (AC).**  Proved from
`LocalDiffusion` alone, through the rectangle symmetry of the killed kernel.
Only the upgrade to *every* starting point is missing. -/
theorem killedKernel_ae_eq_zero (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (t : NNReal)
    {B : Set (Vec d)} (hB : MeasurableSet B)
    (hBnull : ((weightedMeasure rho).restrict U) B = 0) :
    ∀ᵐ x ∂((weightedMeasure rho).restrict U), killedKernel law U hU t x B = 0 := by
  set mu := (weightedMeasure rho).restrict U with hmu
  have hsym := killedKernel_rectangle_symmetry hD hU hUb t univ B MeasurableSet.univ hB
  have hle : (∫⁻ x in B, killedKernel law U hU t x univ ∂mu) ≤ 0 := by
    calc
      (∫⁻ x in B, killedKernel law U hU t x univ ∂mu) ≤ ∫⁻ _x in B, (1 : ℝ≥0∞) ∂mu :=
        lintegral_mono fun x => (killedKernel_subMarkov law U hU t).measure_le_one x univ
      _ = mu B := by rw [setLIntegral_const, one_mul]
      _ = 0 := hBnull
  have hzero : (∫⁻ x, killedKernel law U hU t x B ∂mu) = 0 := by
    have := hsym.trans (le_antisymm hle bot_le)
    rwa [Measure.restrict_univ] at this
  have hmeas : Measurable fun x => killedKernel law U hU t x B :=
    (killedKernel law U hU t).measurable_coe hB
  exact (lintegral_eq_zero_iff hmeas).mp hzero

/-- **(AC) holds for almost every starting point.**  The raw-law form of
`killedKernel_ae_eq_zero`: `LocalDiffusion` alone already gives every clause of
`KilledLawAbsolutelyContinuousOn` except the quantifier `∀ x ∈ U`, which it
weakens to `∀ᵐ x` (and needs no positivity of the time). -/
theorem killedLaw_ae_eq_zero (hD : LocalDiffusion c rho law)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (t : ℝ)
    {B : Set (Vec d)} (hB : MeasurableSet B)
    (hBnull : (weightedMeasure rho) (B ∩ U) = 0) :
    ∀ᵐ x ∂((weightedMeasure rho).restrict U),
      law x {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
        LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} = 0 := by
  haveI : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
  haveI : IsFiniteMeasure ((weightedMeasure rho).restrict U) :=
    isFiniteMeasure_restrict (weightedMeasure_ne_top_of_localDiffusion hD hU hUb)
  have hres : ((weightedMeasure rho).restrict U) B = 0 := by
    rwa [Measure.restrict_apply hB]
  filter_upwards [killedKernel_ae_eq_zero hD hU hUb (Real.toNNReal t) hB hres] with x hx
  rwa [killedKernel_apply_law law hU t x B hB] at hx

/-! ## The construction -/

/-- (AC) makes the killed kernel absolutely continuous at every point of `U`. -/
theorem absolutelyContinuous_killedKernel
    (hac : KilledLawAbsolutelyContinuousOn law rho U) (hU : IsOpen U)
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    killedKernel law U hU (Real.toNNReal t) x ≪ (weightedMeasure rho).restrict U := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.restrict_apply hs] at hs0
  rw [killedKernel_apply_law law hU t x s hs]
  exact hac t ht x hx s hs hs0

/-- **The killed transition density exists.**  From `LocalDiffusion`, an open
bounded domain and the absolute-continuity condition (AC), the kernel
Radon–Nikodym derivative of the killed kernel against the weighted measure is a
killed density in the sense of `IsKilledDensity`. -/
theorem exists_isKilledDensity_of_localDiffusion (hD : LocalDiffusion c rho law)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hac : KilledLawAbsolutelyContinuousOn law rho U) :
    ∃ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p := by
  haveI : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
  haveI hfinite : IsFiniteMeasure ((weightedMeasure rho).restrict U) :=
    isFiniteMeasure_restrict (weightedMeasure_ne_top_of_localDiffusion hD hU hUb)
  set eta : Kernel (Vec d) (Vec d) :=
    Kernel.const (Vec d) ((weightedMeasure rho).restrict U) with heta
  refine ⟨fun t x y =>
    (((killedKernel law U hU (Real.toNNReal t)).rnDeriv eta) x y).toReal, ?_, ?_, ?_⟩
  · intro t _
    exact (Kernel.measurable_rnDeriv _ eta).ennreal_toReal
  · intro t _ x _ y _
    exact ENNReal.toReal_nonneg
  · intro t ht x hx B hB
    haveI : IsFiniteKernel (killedKernel law U hU (Real.toNNReal t)) :=
      (killedKernel_subMarkov law U hU (Real.toNNReal t)).isFiniteKernel
    have hac' := absolutelyContinuous_killedKernel hac hU ht hx
    have hconst : eta x = (weightedMeasure rho).restrict U := rfl
    rw [← killedKernel_apply_law law hU t x B hB,
      ← Kernel.setLIntegral_rnDeriv (hconst ▸ hac') hB, hconst,
      ← Measure.restrict_restrict hB]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae
      (Kernel.rnDeriv_ne_top (killedKernel law U hU (Real.toNNReal t)) eta
        (a := x))] with y hy
    exact (ENNReal.ofReal_toReal hy).symm

/-- Conversely, a killed density forces (AC). -/
theorem killedLawAbsolutelyContinuousOn_of_isKilledDensity {p : ℝ → Vec d → Vec d → ℝ}
    (hp : IsKilledDensity law rho U p) : KilledLawAbsolutelyContinuousOn law rho U := by
  intro t ht x hx B hB hnull
  rw [hp.2.2 t ht x hx B hB]
  exact setLIntegral_measure_zero _ _ hnull

/-- **(AC) is exactly the missing input.**  Under `LocalDiffusion` on a bounded
open domain, the existence of a killed density is *equivalent* to the
absolute-continuity condition; no construction can dispense with it. -/
theorem exists_isKilledDensity_iff (hD : LocalDiffusion c rho law)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    (∃ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p)
      ↔ KilledLawAbsolutelyContinuousOn law rho U :=
  ⟨fun ⟨_, hp⟩ => killedLawAbsolutelyContinuousOn_of_isKilledDensity hp,
    exists_isKilledDensity_of_localDiffusion hD hU hUb⟩



theorem not_exists_isKilledDensity_of_singular {t : ℝ} (ht : 0 < t) {x : Vec d}
    (hx : x ∈ U) {B : Set (Vec d)} (hB : MeasurableSet B)
    (hBnull : (weightedMeasure rho) (B ∩ U) = 0)
    (hpos : law x {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
      LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} ≠ 0) :
    ¬ ∃ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p := by
  rintro ⟨p, hp⟩
  exact hpos
    (killedLawAbsolutelyContinuousOn_of_isKilledDensity hp t ht x hx B hB hBnull)



theorem hasContinuousKilledDensityOn_of_continuousOn (hD : LocalDiffusion c rho law)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hac : KilledLawAbsolutelyContinuousOn law rho U)
    (hcont : ∀ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p →
      ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U)) :
    HasContinuousKilledDensityOn rho law U := by
  obtain ⟨p, hp⟩ := exists_isKilledDensity_of_localDiffusion hD hU hUb hac
  exact ⟨p, hp, hcont p hp⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
