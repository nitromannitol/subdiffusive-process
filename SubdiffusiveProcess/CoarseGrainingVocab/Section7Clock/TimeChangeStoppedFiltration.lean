import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeStoppingTime
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeProcessOccupation

/-!
# The time-changed process is adapted to the stopped filtration

For the conditional form of the Markov property of the time-changed process
(`TimeChangeMarkovProperty.timeChanged_restrict_map_shift`) one must know that
the past of `Y` up to time `t` is an event of the stopped sigma-algebra of the
inverse clock `θ_t`.  This file proves the pointwise version of that statement:
for `s ≤ t` the state

`Y_s(ω) = ω(θ_s(ω))`

is measurable for the stopped sigma-algebra of `θ_t`.  The mechanism is that on
`{θ_t ≤ i}` the inverse clock at level `s ≤ t` is unchanged by stopping the
path at `i`, so `Y_s` is a Borel functional of the stopped path.

On the divergence event `Y_s(ω)` is exactly the time-changed path evaluated at
`s`, which is recorded here as well.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal

noncomputable section

variable {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}

/-- An extended nonnegative real is determined by which finite values dominate
it. -/
theorem eq_of_forall_le_coe_iff {u v : ℝ≥0∞}
    (h : ∀ j : ℝ≥0, u ≤ (j : ℝ≥0∞) ↔ v ≤ (j : ℝ≥0∞)) : u = v := by
  rcases lt_trichotomy u v with hlt | heq | hgt
  · exfalso
    have hu : u ≠ ⊤ := ne_top_of_lt hlt
    have hle : v ≤ ((u.toNNReal : ℝ≥0) : ℝ≥0∞) :=
      (h u.toNNReal).1 (by rw [ENNReal.coe_toNNReal hu])
    rw [ENNReal.coe_toNNReal hu] at hle
    exact absurd hle (not_le.mpr hlt)
  · exact heq
  · exfalso
    have hv : v ≠ ⊤ := ne_top_of_lt hgt
    have hle : u ≤ ((v.toNNReal : ℝ≥0) : ℝ≥0∞) :=
      (h v.toNNReal).2 (by rw [ENNReal.coe_toNNReal hv])
    rw [ENNReal.coe_toNNReal hv] at hle
    exact absurd hle (not_le.mpr hgt)

/-- The inverse clock is monotone in the level. -/
theorem timeChangeRationalInverse_mono_level (s t : NNReal) (hst : s ≤ t)
    (omega : ContinuousPath (State d)) :
    timeChangeRationalInverse a theta s omega ≤
      timeChangeRationalInverse a theta t omega := by
  refine iInf_mono fun q ↦ ?_
  by_cases hcross : (t : ℝ) < timeChangePathClock a theta omega (q : ℝ)
  · rw [if_pos hcross, if_pos ((NNReal.coe_le_coe.mpr hst).trans_lt hcross)]
  · rw [if_neg hcross]
    exact le_top

/-- Stopping the path after the inverse clock has fired does not change the
inverse clock. -/
theorem timeChangeRationalInverse_stoppedPath (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (omega : ContinuousPath (State d))
    (s i : NNReal)
    (hsi : timeChangeRationalInverse a theta s omega ≤ (i : ℝ≥0∞)) :
    timeChangeRationalInverse a theta s
        (ContinuousPath.stoppedPath (alpha := State d) i omega) =
      timeChangeRationalInverse a theta s omega := by
  have hclock_i : (s : ℝ) ≤ timeChangePathClock a theta omega (i : ℝ) :=
    (timeChangeRationalInverse_le_iff ha hapos s i omega).mp hsi
  refine eq_of_forall_le_coe_iff fun j ↦ ?_
  rw [timeChangeRationalInverse_le_iff ha hapos s j,
    timeChangeRationalInverse_le_iff ha hapos s j]
  rcases le_or_gt j i with hji | hij
  · rw [timeChangePathClock_stoppedPath omega i j.coe_nonneg
      (NNReal.coe_le_coe.mpr hji)]
  · have hmono_stopped :=
      (timeChangePathClock_core_clauses ha hapos 0
        (ContinuousPath.stoppedPath (alpha := State d) i omega)).1
    have hmono := (timeChangePathClock_core_clauses ha hapos 0 omega).1
    have hij' : (i : ℝ) ≤ (j : ℝ) := NNReal.coe_le_coe.mpr hij.le
    have hstopped_i : timeChangePathClock a theta
        (ContinuousPath.stoppedPath (alpha := State d) i omega) (i : ℝ) =
        timeChangePathClock a theta omega (i : ℝ) :=
      timeChangePathClock_stoppedPath omega i i.coe_nonneg le_rfl
    constructor
    · intro _
      exact hclock_i.trans (hmono hij')
    · intro _
      refine hclock_i.trans ?_
      rw [← hstopped_i]
      exact hmono_stopped hij'

/-- The state of the time-changed process, read directly off the input path. -/
def timeChangedValue (a : Theta → State d → ℝ) (theta : Theta) (s : NNReal)
    (omega : ContinuousPath (State d)) : State d :=
  omega (timeChangeRationalInverseNNReal a theta s omega)

theorem measurable_timeChangedValue (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (s : NNReal) :
    Measurable (timeChangedValue a theta s) :=
  ContinuousPath.measurable_eval_of_measurable _
    (measurable_timeChangeRationalInverseNNReal ha hapos s)

/-- Once the inverse clock has fired, the time-changed state is a functional of
the stopped path. -/
theorem timeChangedValue_stoppedPath (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (omega : ContinuousPath (State d))
    (s i : NNReal)
    (hsi : timeChangeRationalInverse a theta s omega ≤ (i : ℝ≥0∞)) :
    timeChangedValue a theta s
        (ContinuousPath.stoppedPath (alpha := State d) i omega) =
      timeChangedValue a theta s omega := by
  have hinv : timeChangeRationalInverseNNReal a theta s
      (ContinuousPath.stoppedPath (alpha := State d) i omega) =
      timeChangeRationalInverseNNReal a theta s omega := by
    rw [timeChangeRationalInverseNNReal, timeChangeRationalInverseNNReal,
      timeChangeRationalInverse_stoppedPath ha hapos omega s i hsi]
  have hle : timeChangeRationalInverseNNReal a theta s omega ≤ i := by
    have hu : timeChangeRationalInverse a theta s omega ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.coe_ne_top) hsi
    have hcoe : ((timeChangeRationalInverseNNReal a theta s omega : ℝ≥0) : ℝ≥0∞) ≤
        (i : ℝ≥0∞) := by
      rw [timeChangeRationalInverseNNReal, ENNReal.coe_toNNReal hu]
      exact hsi
    exact ENNReal.coe_le_coe.mp hcoe
  rw [timeChangedValue, timeChangedValue, hinv,
    ContinuousPath.stoppedPath_apply_of_le i omega _ hle]

/-- **The time-changed process is adapted to the stopped filtration of the
inverse clock.**  For `s ≤ t`, the state of the time-changed process at time
`s` is measurable for the stopped sigma-algebra of `θ_t`. -/
theorem measurableSet_preimage_timeChangedValue (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (default : ContinuousPath (State d))
    (s t : NNReal) (hst : s ≤ t) {B : Set (State d)} (hB : MeasurableSet B) :
    MeasurableSet[(isStoppingTime_timeChangeRationalInverse
        (a := a) (theta := theta) ha hapos default t).measurableSpace]
      (timeChangedValue a theta s ⁻¹' B) := by
  refine ⟨(measurable_timeChangedValue ha hapos s) hB, fun i ↦ ?_⟩
  have hkey : (timeChangedValue a theta s ⁻¹' B) ∩
        {omega : ContinuousPath (State d) |
          timeChangeRationalInverse a theta t omega ≤ (i : ℝ≥0∞)} =
      ((fun omega : ContinuousPath (State d) ↦
          timeChangedValue a theta s
            (ContinuousPath.stoppedPath (alpha := State d) i omega)) ⁻¹' B) ∩
        {omega : ContinuousPath (State d) |
          timeChangeRationalInverse a theta t omega ≤ (i : ℝ≥0∞)} := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hmem, hti⟩
      refine ⟨?_, hti⟩
      rw [timeChangedValue_stoppedPath ha hapos omega s i
        ((timeChangeRationalInverse_mono_level s t hst omega).trans hti)]
      exact hmem
    · rintro ⟨hmem, hti⟩
      refine ⟨?_, hti⟩
      rw [← timeChangedValue_stoppedPath ha hapos omega s i
        ((timeChangeRationalInverse_mono_level s t hst omega).trans hti)]
      exact hmem
  refine MeasurableSet.congr ?_ hkey.symm
  refine MeasurableSet.inter ?_ ?_
  · exact ((measurable_timeChangedValue ha hapos s).comp
      (measurable_stoppedPath_canonicalFiltration default i)) hB
  · have hmeas : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := State d) i]
        {omega : ContinuousPath (State d) |
          (t : ℝ) ≤ timeChangePathClock a theta omega (i : ℝ)} :=
      measurableSet_le measurable_const
        (measurable_timeChangePathClock_canonicalFiltration ha hapos default i)
    refine MeasurableSet.congr hmeas ?_
    ext omega
    exact (timeChangeRationalInverse_le_iff ha hapos t i omega).symm

/-- On the divergence event, the time-changed state is the time-changed path
evaluated at the same time. -/
theorem measurableTimeChangedContinuousPath_apply_eq_timeChangedValue
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (s : NNReal)
    {omega : ContinuousPath (State d)}
    (homega : omega ∈ timeChangeUnboundedEvent a theta) :
    measurableTimeChangedContinuousPath a theta ha hapos default omega s =
      timeChangedValue a theta s omega := by
  have hunbomega := (mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega
  rw [measurableTimeChangedContinuousPath_eq_timeChangedPath ha hapos default homega,
    timeChangedValue,
    timeChangeRationalInverseNNReal_eq_orderIso_symm ha hapos omega hunbomega s]
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
