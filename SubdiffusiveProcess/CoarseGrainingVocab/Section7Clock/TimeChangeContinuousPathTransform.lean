module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangePathClock
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# The continuous path obtained from an unbounded intrinsic clock

For a continuous strictly increasing clock on nonnegative time whose range is
unbounded, the clock is an order isomorphism of `NNReal`.  Composing a
continuous path with its inverse constructs the pathwise time change and
identifies its coordinates with the `sInf` formula in the predicate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MarkovProcess Set
open _root_.SubdiffusiveProcess.Section7
open scoped ENNReal NNReal

noncomputable section

/-- Restriction of a normalized monotone real clock to nonnegative time. -/
def nonnegativeClock (A : ℝ → ℝ) (hA0 : A 0 = 0) (hA : Monotone A) :
    NNReal → NNReal := fun s ↦
  ⟨A s, by
    rw [← hA0]
    exact hA NNReal.zero_le_coe⟩

theorem strictMono_nonnegativeClock {A : ℝ → ℝ} (hA0 : A 0 = 0)
    (hA : Monotone A) (hstrict : StrictMonoOn A (Ici 0)) :
    StrictMono (nonnegativeClock A hA0 hA) := by
  intro s t hst
  exact hstrict (NNReal.zero_le_coe) (NNReal.zero_le_coe)
    (by exact_mod_cast hst)

theorem surjective_nonnegativeClock {A : ℝ → ℝ} (hA0 : A 0 = 0)
    (hA : Monotone A) (hcont : Continuous A)
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < A s) :
    Function.Surjective (nonnegativeClock A hA0 hA) := by
  intro y
  obtain ⟨s, hs, hys⟩ := hunbounded y
  have hy : (y : ℝ) ∈ Icc (A 0) (A s) := by
    rw [hA0]
    exact ⟨NNReal.zero_le_coe, hys.le⟩
  obtain ⟨r, hr, hAr⟩ := intermediate_value_Icc hs hcont.continuousOn hy
  refine ⟨⟨r, hr.1⟩, NNReal.eq ?_⟩
  exact hAr

/-- The order isomorphism associated with a regular unbounded clock. -/
def nonnegativeClockOrderIso (A : ℝ → ℝ) (hA0 : A 0 = 0)
    (hA : Monotone A) (hstrict : StrictMonoOn A (Ici 0))
    (hcont : Continuous A)
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < A s) : OrderIso NNReal NNReal :=
  (strictMono_nonnegativeClock hA0 hA hstrict).orderIsoOfSurjective
    (nonnegativeClock A hA0 hA)
    (surjective_nonnegativeClock hA0 hA hcont hunbounded)

@[simp]
theorem coe_nonnegativeClockOrderIso_apply (A : ℝ → ℝ) (hA0 : A 0 = 0)
    (hA : Monotone A) (hstrict : StrictMonoOn A (Ici 0))
    (hcont : Continuous A)
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < A s) (s : NNReal) :
    ((nonnegativeClockOrderIso A hA0 hA hstrict hcont hunbounded s : NNReal) : ℝ) = A s :=
  rfl

/-- The inverse of the clock order isomorphism is exactly the generalized
inverse written in the time-change predicate. -/
theorem coe_nonnegativeClockOrderIso_symm_eq_sInf
    (A : ℝ → ℝ) (hA0 : A 0 = 0)
    (hA : Monotone A) (hstrict : StrictMonoOn A (Ici 0))
    (hcont : Continuous A)
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < A s) (t : NNReal) :
    ((nonnegativeClockOrderIso A hA0 hA hstrict hcont hunbounded).symm t : ℝ) =
      sInf {s : ℝ | 0 ≤ s ∧ (t : ℝ) < A s} := by
  let e := nonnegativeClockOrderIso A hA0 hA hstrict hcont hunbounded
  have hset : {s : ℝ | 0 ≤ s ∧ (t : ℝ) < A s} = Ioi ((e.symm t : NNReal) : ℝ) := by
    ext s
    constructor
    · rintro ⟨hs, hts⟩
      let sn : NNReal := ⟨s, hs⟩
      have htclock : t < e sn := by
        apply NNReal.coe_lt_coe.mp
        simpa only [e, coe_nonnegativeClockOrderIso_apply] using! hts
      have hinv : e.symm t < sn := e.symm_apply_lt.mpr htclock
      exact_mod_cast hinv
    · intro hinv
      have hs : 0 ≤ s := le_trans NNReal.zero_le_coe (le_of_lt hinv)
      let sn : NNReal := ⟨s, hs⟩
      have hinv' : e.symm t < sn := by exact_mod_cast hinv
      have htclock : t < e sn := e.symm_apply_lt.mp hinv'
      refine ⟨hs, ?_⟩
      have htclock' := NNReal.coe_lt_coe.mpr htclock
      simpa only [e, coe_nonnegativeClockOrderIso_apply] using! htclock'
  rw [hset, csInf_Ioi]

/-- Reparameterize a continuous path by the inverse of a regular unbounded
clock. -/
def timeChangedContinuousPath {alpha : Type*} [TopologicalSpace alpha]
    (omega : ContinuousPath alpha) (A : ℝ → ℝ) (hA0 : A 0 = 0)
    (hA : Monotone A) (hstrict : StrictMonoOn A (Ici 0))
    (hcont : Continuous A)
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < A s) :
    ContinuousPath alpha where
  toFun t := omega ((nonnegativeClockOrderIso A hA0 hA hstrict hcont hunbounded).symm t)
  continuous_toFun := omega.continuous.comp
    (nonnegativeClockOrderIso A hA0 hA hstrict hcont hunbounded).symm.continuous

/-- Coordinates of the reparameterized path have exactly the `sInf`
form. -/
theorem timeChangedContinuousPath_apply_sInf
    {alpha : Type*} [TopologicalSpace alpha]
    (omega : ContinuousPath alpha) (A : ℝ → ℝ) (hA0 : A 0 = 0)
    (hA : Monotone A) (hstrict : StrictMonoOn A (Ici 0))
    (hcont : Continuous A)
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < A s) (t : NNReal) :
    timeChangedContinuousPath omega A hA0 hA hstrict hcont hunbounded t =
      omega (Real.toNNReal (sInf {s : ℝ | 0 ≤ s ∧ (t : ℝ) < A s})) := by
  rw [← coe_nonnegativeClockOrderIso_symm_eq_sInf A hA0 hA hstrict hcont hunbounded t]
  change omega ((nonnegativeClockOrderIso A hA0 hA hstrict hcont hunbounded).symm t) =
    omega (Real.toNNReal
      (((nonnegativeClockOrderIso A hA0 hA hstrict hcont hunbounded).symm t : NNReal) : ℝ))
  rw [Real.toNNReal_coe]

/-- A positive continuous coefficient and an unbounded reciprocal path clock
produce a continuous inverse-clock path satisfying the coordinate
formula. -/
theorem exists_timeChangedContinuousPath
    {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d))
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < timeChangePathClock a theta omega s) :
    ∃ eta : ContinuousPath (State d), ∀ t : NNReal,
      eta t = omega (Real.toNNReal
        (sInf {s : ℝ | 0 ≤ s ∧ (t : ℝ) < timeChangePathClock a theta omega s})) := by
  obtain ⟨hcont, hstrict⟩ := timeChangePathClock_regular ha hapos omega
  obtain ⟨hmono, hzero, _hintegral⟩ := timeChangePathClock_core_clauses ha hapos 0 omega
  exact ⟨timeChangedContinuousPath omega (timeChangePathClock a theta omega)
      hzero hmono hstrict hcont hunbounded,
    timeChangedContinuousPath_apply_sInf omega (timeChangePathClock a theta omega)
      hzero hmono hstrict hcont hunbounded⟩

/-- All pathwise clauses of the intrinsic-time-change predicate hold
for the inverse-clock transform of an input path with unbounded clock.  What
remains at the process level is to make this transform measurable in `omega`
and identify its pushforward law. -/
theorem exists_timeChangedLifetimePath_clock_clauses
    {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (x : State d) (omega : ContinuousPath (State d))
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < timeChangePathClock a theta omega s) :
    ∃ eta : LifetimePath (State d), ∃ A : ℝ → ℝ,
      Monotone A ∧ A 0 = 0 ∧
      (∀ s : ℝ, 0 ≤ s →
        ENNReal.ofReal s < (LifetimePath.ofContinuousPath omega).lifetime →
        A s = ∫ r in (0 : ℝ)..s,
          (a theta (lifetimeValue x (Real.toNNReal r)
            (LifetimePath.ofContinuousPath omega)))⁻¹) ∧
      eta.lifetime =
        sSup (ENNReal.ofReal ''
          (A '' {s : ℝ | 0 ≤ s ∧
            ENNReal.ofReal s < (LifetimePath.ofContinuousPath omega).lifetime})) ∧
      ∀ t : NNReal, ENNReal.ofNNReal t < eta.lifetime →
        LifetimePath.coordinate t eta =
          LifetimePath.coordinate
            (Real.toNNReal (sInf {s : ℝ | 0 ≤ s ∧ (t : ℝ) < A s}))
            (LifetimePath.ofContinuousPath omega) := by
  let A := timeChangePathClock a theta omega
  obtain ⟨hcont, hstrict⟩ := timeChangePathClock_regular ha hapos omega
  obtain ⟨hmono, hzero, hintegral⟩ := timeChangePathClock_core_clauses ha hapos x omega
  let etaC := timeChangedContinuousPath omega A hzero hmono hstrict hcont hunbounded
  refine ⟨LifetimePath.ofContinuousPath etaC, A, hmono, hzero, hintegral, ?_, ?_⟩
  · change (∞ : ENNReal) = sSup (ENNReal.ofReal ''
      (A '' {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < ∞}))
    exact (sSup_ofReal_clock_before_top_eq_top hunbounded).symm
  · intro t _ht
    rw [LifetimePath.coordinate_ofContinuousPath,
      LifetimePath.coordinate_ofContinuousPath]
    congr 1
    exact timeChangedContinuousPath_apply_sInf omega A hzero hmono hstrict hcont hunbounded t

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
