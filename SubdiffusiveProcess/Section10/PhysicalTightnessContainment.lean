import SubdiffusiveProcess.Section10.PhysicalTightnessClocks
import SubdiffusiveProcess.Section10.PhysicalTightnessNonexplosion

/-!
# Annealed containment and simultaneous nonexplosion from large-cube exit bounds

The quantitative input is an early-exit estimate with an integrable random
constant, at arbitrarily large triadic cubes. The clock lower bound is proved
for each physical branch in `PhysicalTightnessClocks`. This reduction neither
assumes conservativity nor requires measurability of a supremum over starts.
Its remaining early-exit supplier is explicit; it does not close the paper root.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- A measurable a.e. bound can be made a bound at every environment by setting
it to one on a measurable null set. No measurability of the bounded family is needed. -/
theorem measurable_majorant_of_ae {Ω Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : Set Z) (f : Ω → Z → ENNReal) (g : Ω → ENNReal)
    (hg : Measurable g) (hpoint : ∀ᵐ ω ∂μ, ∀ x ∈ B, f ω x ≤ g ω)
    (hprob : ∀ ω x, f ω x ≤ 1) :
    ∃ G : Ω → ENNReal, Measurable G ∧
      (∀ ω, ∀ x ∈ B, f ω x ≤ G ω) ∧ ∫⁻ ω, G ω ∂μ = ∫⁻ ω, g ω ∂μ := by
  classical
  let bad : Set Ω := toMeasurable μ {ω | ¬ ∀ x ∈ B, f ω x ≤ g ω}
  have hbad : μ bad = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hpoint
  let G : Ω → ENNReal := fun ω => if ω ∈ bad then 1 else g ω
  refine ⟨G, Measurable.ite (measurableSet_toMeasurable _ _) measurable_const hg, ?_, ?_⟩
  · intro ω x hx
    by_cases hω : ω ∈ bad
    · simpa only [G, if_pos hω] using hprob ω x
    · simp only [G, if_neg hω]
      by_contra hf
      exact hω (subset_toMeasurable μ _ (fun hall => hf (hall x hx)))
  · apply lintegral_congr_ae
    have hgood : ∀ᵐ ω ∂μ, ω ∉ bad := by
      rw [ae_iff]
      simpa using hbad
    filter_upwards [hgood] with ω hω
    simp only [G, if_neg hω]

/-- A large-cube clock of at least `3^(2j)` converts the uniform local estimate
into arbitrarily small all-environment measurable containment majorants. -/
theorem annealed_containment_of_large_cube_exit {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (LN : ℕ → Kernel (Ω × Vec d) (Path d)) (hLN : ∀ N, IsMarkovKernel (LN N))
    (timeUnit : ℕ → ℕ → ℝ) (htime : ∀ N j, (3 : ℝ) ^ (2 * j) ≤ timeUnit N j)
    (C : ℝ) (hC : 0 ≤ C)
    (hfast : ∀ N j : ℕ, ∃ K : Ω → ℝ, Measurable K ∧ (∀ ω, 0 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω) ∂μ) ≤ ENNReal.ofReal C ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 < t → ∀ x ∈ Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 18),
        LN N (ω, x) {w | LifetimePath.exitTime (Metric.ball (0 : Vec d)
          ((3 : ℝ) ^ j / 2)) w ≤ ENNReal.ofReal t} ≤
          ENNReal.ofReal (K ω * Real.sqrt (t / timeUnit N j)))
    (B : Set (Vec d)) (hB : Bornology.IsBounded B) (T : ℝ) (hT : 0 < T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ j : ℕ, ∀ N : ℕ, ∃ G : Ω → ENNReal, Measurable G ∧
      (∀ ω, ∀ x ∈ B, LN N (ω, x)
        {w | LifetimePath.exitTime (Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 2)) w ≤
          ENNReal.ofReal T} ≤ G ω) ∧
      ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hBR⟩ := hB.subset_closedBall (0 : Vec d)
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
    (max (18 * (R + 1)) (C * Real.sqrt T / ε)) (by norm_num : (1 : ℝ) < 3)
  have hr : 0 < (3 : ℝ) ^ j := by positivity
  have hinner : B ⊆ Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 18) := by
    intro x hx
    have hdist := Metric.mem_closedBall.mp (hBR hx)
    have hlarge := (le_max_left (18 * (R + 1)) (C * Real.sqrt T / ε)).trans_lt hj
    exact Metric.mem_ball.mpr (by linarith)
  have hsmall : C * Real.sqrt T / (3 : ℝ) ^ j ≤ ε := by
    have hlarge := (le_max_right (18 * (R + 1)) (C * Real.sqrt T / ε)).trans_lt hj
    apply (div_le_iff₀ hr).2
    have hmul := (div_lt_iff₀ hε).mp hlarge
    nlinarith
  refine ⟨j, ?_⟩
  intro N
  obtain ⟨K, hK, hK0, hmoment, hpoint⟩ := hfast N j
  have htunit : 0 < timeUnit N j := (by positivity : 0 < (3 : ℝ) ^ (2 * j)).trans_le (htime N j)
  have hroot : Real.sqrt (T / timeUnit N j) ≤ Real.sqrt T / (3 : ℝ) ^ j := by
    calc
      Real.sqrt (T / timeUnit N j) ≤ Real.sqrt (T / (3 : ℝ) ^ (2 * j)) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hT.le (by positivity) (htime N j))
      _ = Real.sqrt T / (3 : ℝ) ^ j := by
        rw [Real.sqrt_div hT.le, show (3 : ℝ) ^ (2 * j) = ((3 : ℝ) ^ j) ^ 2 by ring]
        rw [Real.sqrt_sq hr.le]
  let g : Ω → ENNReal := fun ω => ENNReal.ofReal (K ω * Real.sqrt (T / timeUnit N j))
  have hg : Measurable g := ENNReal.measurable_ofReal.comp (hK.mul_const _)
  have hgpoint : ∀ᵐ ω ∂μ, ∀ x ∈ B,
      LN N (ω, x) {w | LifetimePath.exitTime
        (Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 2)) w ≤ ENNReal.ofReal T} ≤ g ω := by
    filter_upwards [hpoint] with ω hω
    intro x hx
    exact hω T hT x (hinner hx)
  have hint : (∫⁻ ω, g ω ∂μ) ≤ ENNReal.ofReal ε := by
    calc
      (∫⁻ ω, g ω ∂μ) = ENNReal.ofReal (Real.sqrt (T / timeUnit N j)) *
          (∫⁻ ω, ENNReal.ofReal (K ω) ∂μ) := by
        have hfun : g = fun ω => ENNReal.ofReal (Real.sqrt (T / timeUnit N j)) *
            ENNReal.ofReal (K ω) := by
          funext ω
          exact (ENNReal.ofReal_mul' (Real.sqrt_nonneg _)).trans (mul_comm _ _)
        rw [hfun]
        exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp hK)
      _ ≤ ENNReal.ofReal (Real.sqrt (T / timeUnit N j)) * ENNReal.ofReal C :=
        mul_le_mul' le_rfl hmoment
      _ = ENNReal.ofReal (C * Real.sqrt (T / timeUnit N j)) := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal
        ((mul_le_mul_of_nonneg_left hroot hC).trans (by simpa [mul_div_assoc] using hsmall))
  haveI := hLN N
  obtain ⟨G, hG, hGpoint, hGint⟩ := measurable_majorant_of_ae μ B
    (fun ω x => LN N (ω, x) {w | LifetimePath.exitTime
      (Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 2)) w ≤ ENNReal.ofReal T}) g hg hgpoint
    (fun ω x => (measure_mono (subset_univ _)).trans (by simp))
  exact ⟨G, hG, hGpoint, hGint.trans_le hint⟩

/-- Step 2: the same large-cube estimates prove one environment event of
nonexplosion for every base cutoff and every start. -/
theorem nonexplosion_of_large_cube_exit {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (LN : ℕ → Kernel (Ω × Vec d) (Path d)) (hLN : ∀ N, IsMarkovKernel (LN N))
    (timeUnit : ℕ → ℕ → ℝ) (htime : ∀ N j, (3 : ℝ) ^ (2 * j) ≤ timeUnit N j)
    (C : ℝ) (hC : 0 ≤ C)
    (hfast : ∀ N j : ℕ, ∃ K : Ω → ℝ, Measurable K ∧ (∀ ω, 0 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω) ∂μ) ≤ ENNReal.ofReal C ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 < t → ∀ x ∈ Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 18),
        LN N (ω, x) {w | LifetimePath.exitTime (Metric.ball (0 : Vec d)
          ((3 : ℝ) ^ j / 2)) w ≤ ENNReal.ofReal t} ≤
          ENNReal.ofReal (K ω * Real.sqrt (t / timeUnit N j))) :
    ∀ᵐ ω ∂μ, ∀ N : ℕ, ∀ x : Vec d, ∀ᵐ w ∂LN N (ω, x), w.lifetime = ⊤ := by
  apply nonexplosion_of_annealed_containment μ LN
  intro N n m ε hε
  obtain ⟨j, hmajorant⟩ := annealed_containment_of_large_cube_exit μ LN hLN timeUnit htime C hC hfast
    (Metric.closedBall (0 : Vec d) (m : ℝ)) (isCompact_closedBall _ _).isBounded
    (n + 1) (by positivity) ε hε
  obtain ⟨G, hG, hpoint, hmoment⟩ := hmajorant N
  refine ⟨Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 2), G, hG, ?_, hmoment⟩
  filter_upwards [] with ω
  intro x hx
  refine (measure_mono ?_).trans (hpoint ω x hx)
  intro w hw
  change LifetimePath.exitTime (Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 2)) w ≤
    (n : ENNReal) at hw
  change LifetimePath.exitTime (Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 2)) w ≤
    ENNReal.ofReal (n + 1)
  refine hw.trans ?_
  have hn : (n : ℝ) ≤ n + 1 := by linarith
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hn

end SubdiffusiveProcess.Section10.PhysicalTightness
