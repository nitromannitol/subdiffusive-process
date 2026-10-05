module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeClockMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeContinuousPathTransform
public import MarkovProcess.Path.RandomShiftMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.FixedClockLifetimeProcess
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Instances.Rat

@[expose] public section

/-!
# Measurable inverse-clock path transformation

For a continuous positive coefficient, the path clock integrates its
reciprocal from zero. On the measurable event that this clock is unbounded,
`measurableTimeChangedLifetimePath` uses the inverse-clock parametrization.
On the complement it uses the identity path. The equality with the intended
inverse clock is characterized by
`timeChangeRationalInverseNNReal_eq_orderIso_symm` on the unbounded-clock
event. Almost-sure clock divergence must be supplied by the probabilistic
construction before the complementary extension can be ignored. Both
branches here have infinite lifetime; that fact alone does not prove divergence.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory MarkovProcess Set
open _root_.SubdiffusiveProcess.Section7
open scoped ENNReal NNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Theta : Type*} {d : ℕ}

/-- The event that the reciprocal additive clock is unbounded, expressed by
the equivalent countable condition at natural times. -/
def timeChangeUnboundedEvent (a : Theta → State d → ℝ) (theta : Theta) :
    Set (ContinuousPath (State d)) :=
  ⋂ n : ℕ, ⋃ k : ℕ,
    {omega | (n : ℝ) < timeChangePathClock a theta omega k}

theorem measurableSet_timeChangeUnboundedEvent
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x) :
    MeasurableSet (timeChangeUnboundedEvent a theta) := by
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_lt measurable_const
    (measurable_timeChangePathClock ha hapos k)

theorem mem_timeChangeUnboundedEvent_iff
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d)) :
    omega ∈ timeChangeUnboundedEvent a theta ↔
      ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < timeChangePathClock a theta omega s := by
  constructor
  · intro h B
    obtain ⟨n, hn⟩ := exists_nat_gt B
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp h n)
    exact ⟨k, by positivity, hn.trans hk⟩
  · intro h
    apply Set.mem_iInter.mpr
    intro n
    obtain ⟨s, hs, hns⟩ := h n
    obtain ⟨k, hsk⟩ := exists_nat_ge s
    apply Set.mem_iUnion.mpr
    refine ⟨k, hns.trans_le ?_⟩
    exact (timeChangePathClock_core_clauses ha hapos 0 omega).1 hsk

/-- A countable representation of the inverse clock.  Noncrossing rational
times contribute `∞`; crossing rational times contribute their time. -/
def timeChangeRationalInverse (a : Theta → State d → ℝ) (theta : Theta)
    (t : NNReal) (omega : ContinuousPath (State d)) : ENNReal :=
  ⨅ q : ℚ≥0,
    if (t : ℝ) < timeChangePathClock a theta omega (q : ℝ)
    then ENNReal.ofReal (q : ℝ) else ∞

theorem measurable_timeChangeRationalInverse
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x) (t : NNReal) :
    Measurable (timeChangeRationalInverse a theta t) := by
  apply Measurable.iInf
  intro q
  apply Measurable.ite
  · exact measurableSet_lt measurable_const
      (measurable_timeChangePathClock ha hapos (q : ℝ))
  · exact measurable_const
  · exact measurable_const

/-- The finite readout of the rational inverse is measurable.  On the
unbounded-clock event the value is finite and is the genuine inverse. -/
def timeChangeRationalInverseNNReal (a : Theta → State d → ℝ) (theta : Theta)
    (t : NNReal) (omega : ContinuousPath (State d)) : NNReal :=
  (timeChangeRationalInverse a theta t omega).toNNReal

theorem measurable_timeChangeRationalInverseNNReal
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x) (t : NNReal) :
    Measurable (timeChangeRationalInverseNNReal a theta t) :=
  ENNReal.measurable_toNNReal.comp
    (measurable_timeChangeRationalInverse ha hapos t)

/-- On an unbounded regular clock, the countable rational inverse is exactly
the inverse order isomorphism. -/
theorem timeChangeRationalInverse_eq_orderIso_symm
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d))
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧
      B < timeChangePathClock a theta omega s) (t : NNReal) :
    timeChangeRationalInverse a theta t omega =
      ((nonnegativeClockOrderIso (timeChangePathClock a theta omega)
        (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
        (timeChangePathClock_core_clauses ha hapos 0 omega).1
        (timeChangePathClock_regular ha hapos omega).2
        (timeChangePathClock_regular ha hapos omega).1 hunbounded).symm t : NNReal) := by
  let A := timeChangePathClock a theta omega
  obtain ⟨hmono, hzero, _⟩ := timeChangePathClock_core_clauses ha hapos 0 omega
  obtain ⟨hcont, hstrict⟩ := timeChangePathClock_regular ha hapos omega
  let e := nonnegativeClockOrderIso A hzero hmono hstrict hcont hunbounded
  change (⨅ q : ℚ≥0, if (t : ℝ) < A (q : ℝ)
    then ENNReal.ofReal (q : ℝ) else ∞) = ((e.symm t : NNReal) : ENNReal)
  apply le_antisymm
  · by_contra hle
    have hlt : ((e.symm t : NNReal) : ENNReal) <
        ⨅ q : ℚ≥0, if (t : ℝ) < A (q : ℝ)
          then ENNReal.ofReal (q : ℝ) else ∞ := lt_of_not_ge hle
    obtain ⟨q, hqnonneg, hthetaq, hqinf⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt
    let qn : ℚ≥0 := ⟨q, hqnonneg⟩
    have hqn : (Real.toNNReal q : NNReal) = (qn : NNReal) := by
      apply NNReal.eq
      rw [Real.coe_toNNReal', max_eq_left (Rat.cast_nonneg.mpr hqnonneg)]
      rfl
    have hinvlt : e.symm t < (qn : NNReal) := by
      rw [← hqn]
      exact ENNReal.coe_lt_coe.mp hthetaq
    have htclockNN : t < e (qn : NNReal) := e.symm_apply_lt.mp hinvlt
    have htclock : (t : ℝ) < A (qn : ℝ) := by
      exact NNReal.coe_lt_coe.mp (by
        simpa only [e, coe_nonnegativeClockOrderIso_apply] using! htclockNN)
    have hiInfLe : (⨅ q : ℚ≥0, if (t : ℝ) < A (q : ℝ)
          then ENNReal.ofReal (q : ℝ) else ∞) ≤ ENNReal.ofReal (qn : ℝ) := by
      exact (iInf_le _ qn).trans_eq (ite_eq_left htclock)
    have hofReal : ENNReal.ofReal (qn : ℝ) =
        ((Real.toNNReal q : NNReal) : ENNReal) := by
      rw [ENNReal.ofReal_eq_coe_nnreal]
      congr 1
      exact hqn.symm
    rw [hofReal] at hiInfLe
    exact (not_lt_of_ge hiInfLe) hqinf
  · apply le_iInf
    intro q
    split_ifs with hcross
    · have htclockNN : t < e (q : NNReal) := by
        apply NNReal.coe_lt_coe.mp
        simpa only [e, coe_nonnegativeClockOrderIso_apply] using! hcross
      have hinv : e.symm t < (q : NNReal) := e.symm_apply_lt.mpr htclockNN
      have hofReal : ENNReal.ofReal (q : ℝ) = ((q : NNReal) : ENNReal) := by
        rw [ENNReal.ofReal_eq_coe_nnreal (show 0 ≤ (q : ℝ) by positivity)]
        congr
      rw [hofReal]
      exact ENNReal.coe_le_coe.mpr hinv.le
    · exact le_top

theorem timeChangeRationalInverseNNReal_eq_orderIso_symm
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d))
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧
      B < timeChangePathClock a theta omega s) (t : NNReal) :
    timeChangeRationalInverseNNReal a theta t omega =
      (nonnegativeClockOrderIso (timeChangePathClock a theta omega)
        (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
        (timeChangePathClock_core_clauses ha hapos 0 omega).1
        (timeChangePathClock_regular ha hapos omega).2
        (timeChangePathClock_regular ha hapos omega).1 hunbounded).symm t := by
  rw [timeChangeRationalInverseNNReal,
    timeChangeRationalInverse_eq_orderIso_symm ha hapos omega hunbounded t,
    ENNReal.toNNReal_coe]

/-- The measurable candidate for the time change.  On paths with unbounded
clock it is the inverse-clock reparameterization; outside that measurable
event it is set to the identity.  The latter branch is irrelevant as soon as
the probabilistic producer proves clock divergence almost surely. -/
def measurableTimeChangedLifetimePath
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d)) : LifetimePath (State d) :=
  if h : omega ∈ timeChangeUnboundedEvent a theta then
    let hunbounded := (mem_timeChangeUnboundedEvent_iff ha hapos omega).mp h
    let hcore := timeChangePathClock_core_clauses ha hapos 0 omega
    let hregular := timeChangePathClock_regular ha hapos omega
    LifetimePath.ofContinuousPath
      (timeChangedContinuousPath omega (timeChangePathClock a theta omega)
        hcore.2.1 hcore.1 hregular.2 hregular.1 hunbounded)
  else
    LifetimePath.ofContinuousPath omega

@[simp]
theorem measurableTimeChangedLifetimePath_lifetime
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d)) :
    (measurableTimeChangedLifetimePath a theta ha hapos omega).lifetime = ∞ := by
  rw [measurableTimeChangedLifetimePath]
  split <;> rfl

theorem measurableTimeChangedLifetimePath_coordinate
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (t : NNReal) (omega : ContinuousPath (State d)) :
    LifetimePath.coordinate t
        (measurableTimeChangedLifetimePath a theta ha hapos omega) =
      if omega ∈ timeChangeUnboundedEvent a theta then
        MarkovProcess.Cemetery.alive
          (omega (timeChangeRationalInverseNNReal a theta t omega))
      else MarkovProcess.Cemetery.alive (omega t) := by
  rw [measurableTimeChangedLifetimePath]
  split_ifs with h
  · let hunbounded := (mem_timeChangeUnboundedEvent_iff ha hapos omega).mp h
    rw [LifetimePath.coordinate_ofContinuousPath]
    change MarkovProcess.Cemetery.alive
        (timeChangedContinuousPath omega (timeChangePathClock a theta omega)
          (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
          (timeChangePathClock_core_clauses ha hapos 0 omega).1
          (timeChangePathClock_regular ha hapos omega).2
          (timeChangePathClock_regular ha hapos omega).1 hunbounded t) = _
    rw [show timeChangeRationalInverseNNReal a theta t omega =
        (nonnegativeClockOrderIso (timeChangePathClock a theta omega)
          (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
          (timeChangePathClock_core_clauses ha hapos 0 omega).1
          (timeChangePathClock_regular ha hapos omega).2
          (timeChangePathClock_regular ha hapos omega).1 hunbounded).symm t from
      timeChangeRationalInverseNNReal_eq_orderIso_symm ha hapos omega hunbounded t]
    rfl
  · exact LifetimePath.coordinate_ofContinuousPath omega t

/-- On the unbounded-clock event, the measurable candidate satisfies every
pathwise clause in the intrinsic-time-change predicate. -/
theorem measurableTimeChangedLifetimePath_clock_clauses
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (x : State d) (omega : ContinuousPath (State d))
    (homega : omega ∈ timeChangeUnboundedEvent a theta) :
    ∃ A : ℝ → ℝ,
      Monotone A ∧ A 0 = 0 ∧
      (∀ s : ℝ, 0 ≤ s →
        ENNReal.ofReal s < (LifetimePath.ofContinuousPath omega).lifetime →
        A s = ∫ r in (0 : ℝ)..s,
          (a theta (lifetimeValue x (Real.toNNReal r)
            (LifetimePath.ofContinuousPath omega)))⁻¹) ∧
      (measurableTimeChangedLifetimePath a theta ha hapos omega).lifetime =
        sSup (ENNReal.ofReal ''
          (A '' {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s <
            (LifetimePath.ofContinuousPath omega).lifetime})) ∧
      ∀ t : NNReal, ENNReal.ofNNReal t <
          (measurableTimeChangedLifetimePath a theta ha hapos omega).lifetime →
        LifetimePath.coordinate t
            (measurableTimeChangedLifetimePath a theta ha hapos omega) =
          LifetimePath.coordinate
            (Real.toNNReal (sInf {s : ℝ | 0 ≤ s ∧ (t : ℝ) < A s}))
            (LifetimePath.ofContinuousPath omega) := by
  let A := timeChangePathClock a theta omega
  have hunbounded := (mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega
  obtain ⟨hmono, hzero, hintegral⟩ :=
    timeChangePathClock_core_clauses ha hapos x omega
  refine ⟨A, hmono, hzero, hintegral, ?_, ?_⟩
  · rw [measurableTimeChangedLifetimePath_lifetime]
    exact (sSup_ofReal_clock_before_top_eq_top hunbounded).symm
  · intro t _ht
    rw [measurableTimeChangedLifetimePath_coordinate]
    simp only [homega, ↓reduceIte, LifetimePath.coordinate_ofContinuousPath]
    rw [timeChangeRationalInverseNNReal_eq_orderIso_symm ha hapos omega hunbounded]
    congr 2
    apply NNReal.eq
    rw [coe_nonnegativeClockOrderIso_symm_eq_sInf A hzero hmono
      (timeChangePathClock_regular ha hapos omega).2
      (timeChangePathClock_regular ha hapos omega).1 hunbounded t]
    exact (Real.coe_toNNReal _ (timeChangeInverseClock_nonneg
      (timeChangeInverseClock_crossing_nonempty hunbounded t))).symm

/-- The inverse-clock reparameterization, with the identity fallback on the
bounded-clock event, is measurable into the coordinate-generated lifetime
path space. -/
theorem measurable_measurableTimeChangedLifetimePath
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x) :
    Measurable (measurableTimeChangedLifetimePath a theta ha hapos) := by
  apply Measurable.of_comap_le
  rw [LifetimePath.instMeasurableSpace, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_iSup]
  apply sup_le
  · rw [MeasurableSpace.comap_comp]
    change MeasurableSpace.comap
      (fun omega : ContinuousPath (State d) ↦
        (measurableTimeChangedLifetimePath a theta ha hapos omega).lifetime)
        inferInstance ≤ borel (ContinuousPath (State d))
    simpa only [measurableTimeChangedLifetimePath_lifetime] using!
      (measurable_const : Measurable
        (fun _omega : ContinuousPath (State d) ↦ (∞ : ENNReal))).comap_le
  · rw [iSup_le_iff]
    intro t
    have hinverse : Measurable
        (timeChangeRationalInverseNNReal a theta t) :=
      measurable_timeChangeRationalInverseNNReal ha hapos t
    have hevalInverse : Measurable
        (fun omega : ContinuousPath (State d) ↦
          omega (timeChangeRationalInverseNNReal a theta t omega)) :=
      ContinuousPath.measurable_eval_of_measurable _ hinverse
    have hgood : Measurable
        (fun omega : ContinuousPath (State d) ↦ MarkovProcess.Cemetery.alive
          (omega (timeChangeRationalInverseNNReal a theta t omega))) :=
      measurable_inl.comp hevalInverse
    have hbad : Measurable
        (fun omega : ContinuousPath (State d) ↦ MarkovProcess.Cemetery.alive (omega t)) :=
      measurable_inl.comp (ContinuousPath.measurable_coordinateProcess t)
    have hpiece : Measurable
        (fun omega : ContinuousPath (State d) ↦
          if omega ∈ timeChangeUnboundedEvent a theta then
            MarkovProcess.Cemetery.alive
              (omega (timeChangeRationalInverseNNReal a theta t omega))
          else MarkovProcess.Cemetery.alive (omega t)) :=
      hgood.piecewise (measurableSet_timeChangeUnboundedEvent ha hapos) hbad
    have hcoordinate :
        (fun omega : ContinuousPath (State d) ↦ LifetimePath.coordinate t
          (measurableTimeChangedLifetimePath a theta ha hapos omega)) =
        fun omega : ContinuousPath (State d) ↦
          if omega ∈ timeChangeUnboundedEvent a theta then
            MarkovProcess.Cemetery.alive
              (omega (timeChangeRationalInverseNNReal a theta t omega))
          else MarkovProcess.Cemetery.alive (omega t) := by
      funext omega
      exact measurableTimeChangedLifetimePath_coordinate a theta ha hapos t omega
    rw [MeasurableSpace.comap_comp]
    change MeasurableSpace.comap
      (fun omega : ContinuousPath (State d) ↦ LifetimePath.coordinate t
        (measurableTimeChangedLifetimePath a theta ha hapos omega)) inferInstance ≤
      borel (ContinuousPath (State d))
    rw [hcoordinate]
    exact hpiece.comap_le

/-- A total measurable reconstruction of an ordinary continuous path from a
lifetime path.  It reads the countable dense-time live coordinates, using the
default path only when a coordinate is already at the cemetery state, and
then applies the library's measurable total continuous extension. -/
def continuousPathOfLifetimePath (default : ContinuousPath (State d))
    (path : LifetimePath (State d)) : ContinuousPath (State d) :=
  ContinuousPath.continuousExtension default fun q : DenseTime ↦
    lifetimeValue (default (DenseTime.castOrderEmbedding q))
      (DenseTime.castOrderEmbedding q) path

theorem measurable_continuousPathOfLifetimePath
    (default : ContinuousPath (State d)) :
    Measurable (continuousPathOfLifetimePath default) := by
  apply (ContinuousPath.measurable_continuousExtension default).comp
  rw [measurable_pi_iff]
  intro q
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.measurable_lifetimeValue
    (default (DenseTime.castOrderEmbedding q)) (DenseTime.castOrderEmbedding q)

@[simp]
theorem continuousPathOfLifetimePath_ofContinuousPath
    (default omega : ContinuousPath (State d)) :
    continuousPathOfLifetimePath default (LifetimePath.ofContinuousPath omega) = omega := by
  rw [continuousPathOfLifetimePath]
  have hfun : (fun q : DenseTime ↦
      lifetimeValue (default (DenseTime.castOrderEmbedding q))
        (DenseTime.castOrderEmbedding q) (LifetimePath.ofContinuousPath omega)) =
      ContinuousPath.denseRestriction omega := by
    funext q
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.lifetimeValue_ofContinuousPath
      (default (DenseTime.castOrderEmbedding q)) (DenseTime.castOrderEmbedding q) omega
  rw [hfun, ContinuousPath.continuousExtension_denseRestriction]

theorem continuousPathOfLifetimePath_of_lifetime_eq_top
    (default : ContinuousPath (State d)) (path : LifetimePath (State d))
    (hpath : path.lifetime = ∞) :
    continuousPathOfLifetimePath default path =
      LifetimePath.toContinuousPath path hpath := by
  conv_lhs => rw [← LifetimePath.ofContinuousPath_toContinuousPath path hpath]
  exact continuousPathOfLifetimePath_ofContinuousPath default _

/-- The measurable lifetime-path endomorphism used by the process-level time
change.  Its restriction to the infinite-lifetime embedding is exactly the
inverse-clock transform constructed above. -/
def measurableTimeChangeLifetimeExtension
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (path : LifetimePath (State d)) :
    LifetimePath (State d) :=
  measurableTimeChangedLifetimePath a theta ha hapos
    (continuousPathOfLifetimePath default path)

theorem measurable_measurableTimeChangeLifetimeExtension
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) :
    Measurable (measurableTimeChangeLifetimeExtension a theta ha hapos default) :=
  (measurable_measurableTimeChangedLifetimePath ha hapos).comp
    (measurable_continuousPathOfLifetimePath default)

@[simp]
theorem measurableTimeChangeLifetimeExtension_ofContinuousPath
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default omega : ContinuousPath (State d)) :
    measurableTimeChangeLifetimeExtension a theta ha hapos default
        (LifetimePath.ofContinuousPath omega) =
      measurableTimeChangedLifetimePath a theta ha hapos omega := by
  rw [measurableTimeChangeLifetimeExtension,
    continuousPathOfLifetimePath_ofContinuousPath]

/-- The total lifetime-path extension satisfies the exact path clauses
on embedded continuous paths whose clock is unbounded. -/
theorem measurableTimeChangeLifetimeExtension_clock_clauses
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (x : State d)
    (omega : ContinuousPath (State d))
    (homega : omega ∈ timeChangeUnboundedEvent a theta) :
    ∃ A : ℝ → ℝ,
      Monotone A ∧ A 0 = 0 ∧
      (∀ s : ℝ, 0 ≤ s →
        ENNReal.ofReal s < (LifetimePath.ofContinuousPath omega).lifetime →
        A s = ∫ r in (0 : ℝ)..s,
          (a theta (lifetimeValue x (Real.toNNReal r)
            (LifetimePath.ofContinuousPath omega)))⁻¹) ∧
      (measurableTimeChangeLifetimeExtension a theta ha hapos default
          (LifetimePath.ofContinuousPath omega)).lifetime =
        sSup (ENNReal.ofReal ''
          (A '' {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s <
            (LifetimePath.ofContinuousPath omega).lifetime})) ∧
      ∀ t : NNReal, ENNReal.ofNNReal t <
          (measurableTimeChangeLifetimeExtension a theta ha hapos default
            (LifetimePath.ofContinuousPath omega)).lifetime →
        LifetimePath.coordinate t
            (measurableTimeChangeLifetimeExtension a theta ha hapos default
              (LifetimePath.ofContinuousPath omega)) =
          LifetimePath.coordinate
            (Real.toNNReal (sInf {s : ℝ | 0 ≤ s ∧ (t : ℝ) < A s}))
            (LifetimePath.ofContinuousPath omega) := by
  simpa only [measurableTimeChangeLifetimeExtension_ofContinuousPath] using!
    measurableTimeChangedLifetimePath_clock_clauses
      a theta ha hapos x omega homega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
