import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.WeightedChaosCutoff
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Lane1.ChaosBasic
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.MeasuresConvergeLocally
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.ContinuousMap.CompactlySupported
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Lane1.ChaosBasic

open Filter MeasureTheory ProbabilityTheory Topology
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The last assertion of G-2 of Proposition `mfd:prop-chaos-growth` (paper
4817-4823): almost surely the limiting measure charges every open set.

This is the only part of the regularity half that does NOT come from the growth
bound, and the paper proves it by a tail argument: for a cube `Q`, the event
`{mu Q = 0}` agrees modulo null sets with `{mu^(>k) Q = 0}` for every `k`,
because the first `k` layers contribute a positive continuous factor; so it is
a tail event of the INDEPENDENT layers and has probability `0` or `1`, and it
is not `1` because the mean mass is the Lebesgue measure of `Q`, which is
positive.

Both halves are carried as hypotheses, at the level of generality the paper
uses them: `hmean`, that the mean mass of a cube is POSITIVE -- the uniform integrability
of the cube-mass martingale, which `\noderef{lem_chaos_moments}` supplies at
`p = 2`, makes it the constant mean of the cutoffs; only its positivity is
used, so that is all the hypothesis asks, and `hzeroone`, Kolmogorov's zero-one law for the
independent layers applied to that event. -/
theorem chaos_full_support
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (mu : BilateralField d → Measure (SpatialCoordinates d))
    (hmeas : Measurable mu)
    (hmean : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      0 < ∫⁻ omega, mu omega (centeredCube z r hr : Set (SpatialCoordinates d))
          ∂(chaosSampleLaw M).toMeasure)
    (hzeroone : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (chaosSampleLaw M).toMeasure
          {omega | mu omega (centeredCube z r hr : Set (SpatialCoordinates d)) = 0} = 0 ∨
        (chaosSampleLaw M).toMeasure
          {omega | mu omega (centeredCube z r hr : Set (SpatialCoordinates d)) = 0} = 1) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, (mu omega).IsOpenPosMeasure := by
  classical
  set P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hP
  -- the countable family of rational cubes
  set z : (Fin d → ℚ) → SpatialCoordinates d := fun q i => ((q i : ℚ) : ℝ) with hz
  set rad : ℕ → ℝ := fun n => 2 / ((n : ℝ) + 1) with hrad
  have hradpos : ∀ n : ℕ, 0 < rad n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [hrad]
    positivity
  -- each rational cube is charged almost surely
  have hpos : ∀ (q : Fin d → ℚ) (n : ℕ),
      P {omega | mu omega (centeredCube (z q) (rad n) (hradpos n) :
        Set (SpatialCoordinates d)) = 0} = 0 := by
    intro q n
    rcases hzeroone (z q) (rad n) (hradpos n) with hzero | hone
    · exact hzero
    · exfalso
      have hmeanq := hmean (z q) (rad n) (hradpos n)
      have hmble : MeasurableSet {omega : BilateralField d |
          mu omega (centeredCube (z q) (rad n) (hradpos n) :
            Set (SpatialCoordinates d)) = 0} := by
        have hm : Measurable fun omega : BilateralField d =>
            mu omega (centeredCube (z q) (rad n) (hradpos n) :
              Set (SpatialCoordinates d)) :=
          Measure.measurable_coe
            ((centeredCube (z q) (rad n) (hradpos n)).isOpen.measurableSet) |>.comp hmeas
        exact hm (measurableSet_singleton 0)
      have hae : ∀ᵐ omega ∂P, mu omega (centeredCube (z q) (rad n) (hradpos n) :
          Set (SpatialCoordinates d)) = 0 := by
        rw [ae_iff]
        have hcompl : P {omega | ¬ mu omega (centeredCube (z q) (rad n) (hradpos n) :
            Set (SpatialCoordinates d)) = 0}
            = P Set.univ - P {omega | mu omega (centeredCube (z q) (rad n) (hradpos n) :
              Set (SpatialCoordinates d)) = 0} := by
          rw [← measure_compl hmble (measure_ne_top P _)]
          rfl
        rw [hcompl, hone]
        simp [hP]
      have hzerointegral : ∫⁻ omega, mu omega (centeredCube (z q) (rad n) (hradpos n) :
          Set (SpatialCoordinates d)) ∂P = 0 := by
        refine lintegral_eq_zero_iff' ?_ |>.mpr hae
        exact (Measure.measurable_coe
          ((centeredCube (z q) (rad n) (hradpos n)).isOpen.measurableSet)).comp
          hmeas |>.aemeasurable
      exact absurd hzerointegral (ne_of_gt hmeanq)
  -- one event for the whole countable family
  have hall : ∀ᵐ omega ∂P, ∀ (q : Fin d → ℚ) (n : ℕ),
      mu omega (centeredCube (z q) (rad n) (hradpos n) :
        Set (SpatialCoordinates d)) ≠ 0 := by
    rw [ae_all_iff]
    intro q
    rw [ae_all_iff]
    intro n
    rw [ae_iff]
    simpa using hpos q n
  filter_upwards [hall] with omega hom
  refine ⟨fun U hU hUne => ?_⟩
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / rho)
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hradlt : rad n < rho / 2 := by
    rw [hrad]
    rw [div_lt_div_iff₀ hnpos (by norm_num : (0:ℝ) < 2)]
    have h4 : 4 / rho < (n : ℝ) := hn
    have : 4 < (n : ℝ) * rho := by
      rw [div_lt_iff₀ hrho] at h4
      linarith
    nlinarith [hrho]
  obtain ⟨q, hq⟩ : ∃ q : Fin d → ℚ, dist (z q) x < rho / 2 := by
    have hchoice : ∀ i : Fin d, ∃ c : ℚ, |x i - (c : ℝ)| < rho / 4 := by
      intro i
      exact exists_rat_near (x i) (by linarith)
    choose c hc using hchoice
    refine ⟨c, ?_⟩
    refine lt_of_le_of_lt ((dist_pi_le_iff (by linarith : (0:ℝ) ≤ rho / 4)).mpr ?_)
      (by linarith)
    intro i
    rw [Real.dist_eq, abs_sub_comm]
    exact (hc i).le
  refine fun hzero => hom q n ?_
  refine measure_mono_null ?_ hzero
  rw [centeredCube_coe_eq_ball]
  intro y hy
  refine hball ?_
  have h1 : dist y (z q) < rad n / 2 := Metric.mem_ball.mp hy
  have h2 : dist y x ≤ dist y (z q) + dist (z q) x := dist_triangle _ _ _
  refine Metric.mem_ball.mpr ?_
  have h3 : rad n / 2 < rho / 4 := by linarith
  linarith

end Paper
