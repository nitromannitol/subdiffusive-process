module

public import SubdiffusiveProcess.Lane1.TailFunctional
public import Mathlib
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.Main.DiffusionPath
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- Source L:298–299 and Fix 9. Pool order `astra10_0927_nondeterministic`; independently harvested. -/
theorem aux_lim_measure_nondeterministic
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : Ω → Measure X)
    (v : Measure X) (hv : v ≠ 0)
    (hmean : ∀ A : Set X, MeasurableSet A → ∫⁻ w, M w A ∂P = v A)
    (hsing : ∀ᵐ w ∂P, M w ⟂ₘ v) :
    ¬ ∃ m : Measure X, ∀ᵐ w ∂P, M w = m := by
  rintro ⟨m, hm⟩
  have hvm : v = m := by
    apply Measure.ext
    intro A hA
    have hae : ∀ᵐ w ∂P, M w A = m A := by
      filter_upwards [hm] with w hw
      rw [hw]
    have h2 : ∫⁻ w, M w A ∂P = m A := by
      rw [lintegral_congr_ae hae, lintegral_const,
        IsProbabilityMeasure.measure_univ, mul_one]
    have h1 : ∫⁻ w, M w A ∂P = v A := hmean A hA
    rw [h2] at h1
    exact h1.symm
  have hsing' : m ⟂ₘ m := by
    haveI : (ae P).NeBot := IsProbabilityMeasure.ae_neBot
    have hboth : ∀ᵐ w ∂P, M w = m ∧ M w ⟂ₘ v := hm.and hsing
    obtain ⟨w, hw⟩ := hboth.exists
    have hthis := hw.2
    rw [hw.1, hvm] at hthis
    exact hthis
  have hm0 : m = 0 := (Measure.MutuallySingular.self_iff m).mp hsing'
  exact hv (by rw [hvm, hm0])

/-- Source Fix 9, L:270–301. Pool order `astra10_0927_set_fatou`; independently harvested. -/
theorem aux_lim_measure_set_fatou
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (S : Set X) (hS : MeasurableSet S) (B : ℕ → Set X)
    (hB : ∀ n, MeasurableSet (B n))
    (hSB : ∀ x ∈ S, ∀ᶠ n in atTop, x ∈ B n) :
    mu S ≤ Filter.liminf (fun n => mu (B n)) atTop := by
  have hpoint :
      (fun x => S.indicator (fun _ : X => (1 : ℝ≥0∞)) x)
        ≤ (fun x => liminf (fun n => (B n).indicator (fun _ : X => (1 : ℝ≥0∞)) x) atTop) := by
    intro x
    change S.indicator (fun _ : X => (1 : ℝ≥0∞)) x ≤
      liminf (fun n => (B n).indicator (fun _ : X => (1 : ℝ≥0∞)) x) atTop
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx (fun _ : X => (1 : ℝ≥0∞))]
      have hcongr : (fun n => (B n).indicator (fun _ : X => (1 : ℝ≥0∞)) x) =ᶠ[atTop]
          (fun _ => (1 : ℝ≥0∞)) := by
        filter_upwards [hSB x hx] with n hn
        exact Set.indicator_of_mem hn (fun _ : X => (1 : ℝ≥0∞))
      rw [Filter.liminf_congr hcongr, Filter.liminf_const]
    · rw [Set.indicator_of_notMem hx (fun _ : X => (1 : ℝ≥0∞))]
      exact zero_le
  have hmeas : ∀ n, Measurable (fun x => (B n).indicator (fun _ : X => (1 : ℝ≥0∞)) x) :=
    fun n => measurable_const.indicator (hB n)
  calc mu S = ∫⁻ x, S.indicator (fun _ : X => (1 : ℝ≥0∞)) x ∂mu :=
        (lintegral_indicator_one hS).symm
    _ ≤ ∫⁻ x, liminf (fun n => (B n).indicator (fun _ : X => (1 : ℝ≥0∞)) x) atTop ∂mu :=
        lintegral_mono hpoint
    _ ≤ liminf (fun n => ∫⁻ x, (B n).indicator (fun _ : X => (1 : ℝ≥0∞)) x ∂mu) atTop :=
        lintegral_liminf_le hmeas
    _ = liminf (fun n => mu (B n)) atTop := by
        apply Filter.liminf_congr
        filter_upwards with n
        exact lintegral_indicator_one (hB n)

/-- Source Fix 9, L:270–301. Pool order `astra10_0927_expected_fatou`; independently harvested. -/
theorem aux_lim_measure_expected_fatou
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Ω → ℝ≥0∞) (b : ℕ → Ω → ℝ≥0∞) (hb : ∀ n, Measurable (b n))
    (C : ℝ≥0∞) (hs : ∀ w, s w ≤ Filter.liminf (fun n => b n w) atTop)
    (hmean : ∀ n, ∫⁻ w, b n w ∂P ≤ C) :
    ∫⁻ w, s w ∂P ≤ C := by
  have h1 : ∫⁻ w, s w ∂P ≤ ∫⁻ w, liminf (fun n => b n w) atTop ∂P :=
    lintegral_mono hs
  have h2 : ∫⁻ w, liminf (fun n => b n w) atTop ∂P
      ≤ liminf (fun n => ∫⁻ w, b n w ∂P) atTop :=
    lintegral_liminf_le hb
  have h3 : liminf (fun n => ∫⁻ w, b n w ∂P) atTop ≤ C :=
    liminf_le_of_frequently_le' (Filter.Frequently.of_forall hmean)
  exact h1.trans (h2.trans h3)

/-- Source Fix 9, L:270–301. Pool order `astra10_0927_expectation_zero`; independently harvested. -/
theorem aux_lim_measure_expectation_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) (b : ℕ → ℝ≥0∞)
    (hb : Tendsto b atTop (𝓝 0)) (hbound : ∀ n, ∫⁻ w, f w ∂P ≤ b n) :
    ∀ᵐ w ∂P, f w = 0 := by
  have hle : ∫⁻ w, f w ∂P ≤ 0 :=
    le_of_tendsto_of_tendsto' (tendsto_const_nhds (x := ∫⁻ w, f w ∂P)) hb (fun n => hbound n)
  have hzero : ∫⁻ w, f w ∂P = 0 := le_antisymm hle (zero_le)
  exact (lintegral_eq_zero_iff hf).mp hzero

/-- Source Fix 9, L:270–301. Pool order `astra10_0927_random_carrier_fatou`; independently harvested. -/
theorem aux_lim_measure_random_carrier_fatou
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (M : Ω → Measure X) (S : Ω → Set X)
    (hS : ∀ w, MeasurableSet (S w)) (hSM : Measurable (fun w => M w (S w)))
    (B : ℕ → ℕ → Ω → Set X) (hB : ∀ j n w, MeasurableSet (B j n w))
    (hBM : ∀ j n, Measurable (fun w => M w (B j n w)))
    (hsub : ∀ j w x, x ∈ S w → ∀ᶠ n in atTop, x ∈ B j n w)
    (b : ℕ → ℝ≥0∞) (hb : Tendsto b atTop (𝓝 0))
    (hmean : ∀ j n, ∫⁻ w, M w (B j n w) ∂P ≤ b j) :
    ∀ᵐ w ∂P, M w (S w) = 0 := by
  refine aux_lim_measure_expectation_zero P (fun w => M w (S w)) hSM b hb ?_
  intro j
  refine aux_lim_measure_expected_fatou P (fun w => M w (S w))
    (fun n w => M w (B j n w)) (hBM j) (b j) ?_ (hmean j)
  intro w
  exact aux_lim_measure_set_fatou (M w) (S w) (hS w) (fun n => B j n w)
    (fun n => hB j n w) (hsub j w)

/-- Fix 9 (L:270–301): the actual density-zero carrier is jointly measurable. -/
theorem aux_lim_measure_measurable_zero_carrier
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    MeasurableSet {q : BilateralField d × SpatialCoordinates d |
      Tendsto (fun N => fineDensity M N q.1 q.2) atTop (𝓝 0)} := by
  exact measurableSet_tendsto (𝓝 0)
    (fun N => (stronglyMeasurable_fineDensity_uncurry M N).measurable)

/-- Fix 9: each point of the carrier eventually lies in each positive-threshold test. -/
theorem aux_lim_measure_zero_carrier_eventually
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : BilateralField d)
    (U : Set (SpatialCoordinates d)) (epsilon : ℝ) (he : 0 < epsilon)
    (x : SpatialCoordinates d) (hx : x ∈ U)
    (hzero : Tendsto (fun N => fineDensity M N omega x) atTop (𝓝 0)) :
    ∀ᶠ N in atTop, x ∈ U ∧ fineDensity M N omega x ≤ epsilon := by
  filter_upwards [hzero.eventually (gt_mem_nhds he)] with N hN
  exact ⟨hx, hN.le⟩

end Paper
