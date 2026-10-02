import SubdiffusiveProcess.Section10.GaussianLawApplications
import MarkovProcess.Trajectory.AllTimeFiniteMarginals

/-!
# One-coordinate singularity of joint and interval laws

Uses the existing `ContinuousPath.finiteEvaluation` and Mathlib's continuous
restriction map. The interval includes its left endpoint zero; the proof
evaluates at the strictly positive midpoint. A continuous Gaussian process is
consumed via its Gaussian evaluation marginals, so no representation of its
mean or covariance (or covariance-rank restriction) is required.
-/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess MarkovProcess
open scoped NNReal

noncomputable section

namespace SubdiffusiveProcess.Section10

/-- Continuous paths on a closed interval of nonnegative time. -/
abbrev IntervalPath (d : ℕ) (s t : ℝ≥0) := C(Set.Icc s t, SpatialCoordinates d)

namespace IntervalPath

/-- The Borel sigma algebra of the compact-open topology on interval paths. -/
instance instMeasurableSpace {d : ℕ} {s t : ℝ≥0} : MeasurableSpace (IntervalPath d s t) :=
  borel _

instance instBorelSpace {d : ℕ} {s t : ℝ≥0} : BorelSpace (IntervalPath d s t) := ⟨rfl⟩

end IntervalPath

/-- A single Gaussian coordinate suffices to separate a joint law from a
Gaussian joint law, with no independence or time-ordering assumptions. -/
theorem finite_time_law_mutuallySingular_gaussian
    {d : ℕ} {I : Type*} [Fintype I]
    (P : Measure (DiffusionPath d)) (times : I → ℝ≥0) (i : I)
    (G : Measure (I → SpatialCoordinates d)) [IsGaussian G]
    (h : ∀ Q : Measure (SpatialCoordinates d), IsGaussian Q →
      P.map (fun w => w (times i)) ⟂ₘ Q) :
    P.map (ContinuousPath.finiteEvaluation times) ⟂ₘ G := by
  let e : (I → SpatialCoordinates d) →L[ℝ] SpatialCoordinates d :=
    ContinuousLinearMap.proj i
  have hGaussian : IsGaussian (G.map e) := inferInstance
  have hs := h (G.map e) hGaussian
  apply mutuallySingular_of_map _ G e e.continuous.measurable
  rw [Measure.map_map e.continuous.measurable
    (ContinuousPath.measurable_finiteEvaluation times)]
  exact hs

/-- G1 joint-law application: any nonempty finite collection of positive times
is singular to every Gaussian law on the full vector of observations. -/
theorem finite_time_law_mutuallySingular_gaussian_of_domination
    {d : ℕ} {I : Type*} [Fintype I] [Nonempty I]
    (mu : Measure (SpatialCoordinates d)) (P : Measure (DiffusionPath d))
    (hs : mu ⟂ₘ volume)
    (hplanes : ∀ L : StrongDual ℝ (SpatialCoordinates d), L ≠ 0 →
      ∀ a : ℝ, mu {x | L x = a} = 0)
    (hP : ∀ t : ℝ≥0, 0 < t → P.map (fun w => w t) ≪ mu)
    (times : I → ℝ≥0) (htimes : ∀ i, 0 < times i)
    (G : Measure (I → SpatialCoordinates d)) [IsGaussian G] :
    P.map (ContinuousPath.finiteEvaluation times) ⟂ₘ G := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact finite_time_law_mutuallySingular_gaussian P times i G
    (dominated_measure_gaussian_singular mu _ hs hplanes (hP _ (htimes i))).2

/-- Separation of an interval law follows from any Gaussian evaluation law at
a strictly positive time in the interval. -/
theorem interval_law_mutuallySingular_of_gaussian_coordinate
    {d : ℕ} (P : Measure (DiffusionPath d)) (s t : ℝ≥0)
    (Q : Measure C(Set.Icc s t, SpatialCoordinates d))
    (r : Set.Icc s t)
    (hQ : IsGaussian (Q.map (fun w => w r)))
    (h : ∀ G : Measure (SpatialCoordinates d), IsGaussian G →
      P.map (fun w => w (r : ℝ≥0)) ⟂ₘ G) :
    P.map (fun w => w.restrict (Set.Icc s t)) ⟂ₘ Q := by
  have he : Measurable (fun w : C(Set.Icc s t, SpatialCoordinates d) => w r) :=
    (continuous_eval_const r).measurable
  have hr : Measurable (fun w : DiffusionPath d => w.restrict (Set.Icc s t)) :=
    (ContinuousMap.continuous_restrict (Set.Icc s t)).measurable
  apply mutuallySingular_of_map _ Q (fun w => w r) he
  rw [Measure.map_map he hr]
  exact h _ hQ

/-- G1 path-law application on every interval `[s,t]`, `0 ≤ s < t`. Every
continuous Gaussian process law satisfies the Gaussian marginal hypothesis.
The strictly positive midpoint also handles `s = 0`. -/
theorem interval_law_mutuallySingular_gaussian_of_domination
    {d : ℕ} (mu : Measure (SpatialCoordinates d)) (P : Measure (DiffusionPath d))
    (hs : mu ⟂ₘ volume)
    (hplanes : ∀ L : StrongDual ℝ (SpatialCoordinates d), L ≠ 0 →
      ∀ a : ℝ, mu {x | L x = a} = 0)
    (hP : ∀ u : ℝ≥0, 0 < u → P.map (fun w => w u) ≪ mu)
    (s t : ℝ≥0) (hst : s < t)
    (Q : Measure C(Set.Icc s t, SpatialCoordinates d))
    (hQ : ∀ r : Set.Icc s t, IsGaussian (Q.map (fun w => w r))) :
    P.map (fun w => w.restrict (Set.Icc s t)) ⟂ₘ Q := by
  have hstR : (s : ℝ) < (t : ℝ) := hst
  let r : Set.Icc s t := ⟨(s + t) / 2, by
    constructor
    · change (s : ℝ) ≤ ((s : ℝ) + (t : ℝ)) / 2
      linarith
    · change ((s : ℝ) + (t : ℝ)) / 2 ≤ (t : ℝ)
      linarith⟩
  have hr : 0 < (r : ℝ≥0) := by
    change (0 : ℝ) < ((s : ℝ) + (t : ℝ)) / 2
    have hs0 : (0 : ℝ) ≤ s := s.property
    linarith
  exact interval_law_mutuallySingular_of_gaussian_coordinate P s t Q r (hQ r)
    (dominated_measure_gaussian_singular mu _ hs hplanes (hP _ hr)).2

/-- A Gaussian measure on continuous interval paths is one concrete instance
of the Gaussian-process comparison above: evaluation is continuous linear. -/
theorem interval_law_mutuallySingular_gaussian
    {d : ℕ} (mu : Measure (SpatialCoordinates d)) (P : Measure (DiffusionPath d))
    (hs : mu ⟂ₘ volume)
    (hplanes : ∀ L : StrongDual ℝ (SpatialCoordinates d), L ≠ 0 →
      ∀ a : ℝ, mu {x | L x = a} = 0)
    (hP : ∀ u : ℝ≥0, 0 < u → P.map (fun w => w u) ≪ mu)
    (s t : ℝ≥0) (hst : s < t)
    (Q : Measure (IntervalPath d s t)) [IsGaussian Q] :
    P.map (fun w => w.restrict (Set.Icc s t)) ⟂ₘ Q := by
  apply interval_law_mutuallySingular_gaussian_of_domination mu P hs hplanes hP s t hst Q
  intro r
  let e : IntervalPath d s t →L[ℝ] SpatialCoordinates d := ContinuousMap.evalCLM ℝ r
  exact (inferInstance : IsGaussian (Q.map e))

end SubdiffusiveProcess.Section10
