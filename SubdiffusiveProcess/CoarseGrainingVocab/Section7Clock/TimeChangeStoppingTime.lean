module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeMeasurableTransform
public import MarkovProcess.Path.Stopping
public import MarkovProcess.Trajectory.StoppingLtTop

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal

noncomputable section

variable {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}

/-! ### The stopped path is adapted -/

/-- Stopping a path at the deterministic time `T` is measurable for the
canonical filtration at time `T`. -/
theorem measurable_stoppedPath_canonicalFiltration
    (default : ContinuousPath (State d)) (T : NNReal) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := State d) T]
      (ContinuousPath.stoppedPath (alpha := State d) T) := by
  have hcoord : ∀ u : NNReal, u ≤ T →
      Measurable[ContinuousPath.canonicalFiltration (alpha := State d) T]
        (fun omega : ContinuousPath (State d) ↦ omega u) := by
    intro u hu
    exact (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (alpha := State d) u).mono
      (ContinuousPath.canonicalFiltration.mono hu) le_rfl
  have hdense : Measurable[ContinuousPath.canonicalFiltration (alpha := State d) T]
      (fun omega : ContinuousPath (State d) ↦
        fun q : DenseTime ↦ omega (min (DenseTime.castOrderEmbedding q) T)) := by
    exact @measurable_pi_lambda _ _ _
      (ContinuousPath.canonicalFiltration (alpha := State d) T) _ _
      (fun q ↦ hcoord _ (min_le_right _ _))
  have heq : ContinuousPath.stoppedPath (alpha := State d) T =
      fun omega : ContinuousPath (State d) ↦
        ContinuousPath.continuousExtension default
          (fun q : DenseTime ↦ omega (min (DenseTime.castOrderEmbedding q) T)) := by
    funext omega
    have hrestrict : (fun q : DenseTime ↦
        omega (min (DenseTime.castOrderEmbedding q) T)) =
        ContinuousPath.denseRestriction
          (ContinuousPath.stoppedPath (alpha := State d) T omega) := by
      funext q
      rw [ContinuousPath.denseRestriction_apply, ContinuousPath.stoppedPath_apply]
    rw [hrestrict, ContinuousPath.continuousExtension_denseRestriction]
  rw [heq]
  exact (ContinuousPath.measurable_continuousExtension default).comp hdense

/-! ### The clock is adapted -/

/-- The clock up to time `T` only sees the path stopped at `T`. -/
theorem timeChangePathClock_stoppedPath (omega : ContinuousPath (State d))
    (T : NNReal) {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ (T : ℝ)) :
    timeChangePathClock a theta
        (ContinuousPath.stoppedPath (alpha := State d) T omega) s =
      timeChangePathClock a theta omega s := by
  rw [timeChangePathClock, timeChangePathClock,
    timeChangeAdditiveClock_eq_integral hs, timeChangeAdditiveClock_eq_integral hs]
  refine intervalIntegral.integral_congr (fun r hr ↦ ?_)
  rw [Set.uIcc_of_le hs] at hr
  have hrT : Real.toNNReal r ≤ T := by
    rw [← Real.toNNReal_coe (r := T)]
    exact Real.toNNReal_le_toNNReal (hr.2.trans hsT)
  simp only [timeChangePathIntegrand]
  rw [ContinuousPath.stoppedPath_apply_of_le T omega _ hrT]

/-- **The intrinsic clock is adapted.**  At every deterministic time the
reciprocal additive clock is measurable for the canonical filtration at that
time. -/
theorem measurable_timeChangePathClock_canonicalFiltration
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (T : NNReal) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := State d) T]
      (fun omega : ContinuousPath (State d) ↦
        timeChangePathClock a theta omega (T : ℝ)) := by
  have hcomp : (fun omega : ContinuousPath (State d) ↦
      timeChangePathClock a theta omega (T : ℝ)) =
      (fun omega : ContinuousPath (State d) ↦
        timeChangePathClock a theta omega (T : ℝ)) ∘
          ContinuousPath.stoppedPath (alpha := State d) T := by
    funext omega
    exact (timeChangePathClock_stoppedPath omega T T.coe_nonneg le_rfl).symm
  rw [hcomp]
  exact (measurable_timeChangePathClock ha hapos (T : ℝ)).comp
    (measurable_stoppedPath_canonicalFiltration default T)

/-! ### The inverse clock is a stopping time -/

/-- The countable inverse clock reaches time `i` exactly when the clock has
reached the level `t` by time `i`. -/
theorem timeChangeRationalInverse_le_iff
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (t i : NNReal) (omega : ContinuousPath (State d)) :
    timeChangeRationalInverse a theta t omega ≤ (i : ℝ≥0∞) ↔
      (t : ℝ) ≤ timeChangePathClock a theta omega (i : ℝ) := by
  obtain ⟨hmono, _, _⟩ := timeChangePathClock_core_clauses ha hapos 0 omega
  obtain ⟨hcont, hstrict⟩ := timeChangePathClock_regular ha hapos omega
  constructor
  · intro hle
    by_contra hlt
    push_neg at hlt
    -- the clock has not reached `t` by time `i`, so by continuity it has not
    -- reached it slightly later either
    have hopen : IsOpen ((timeChangePathClock a theta omega) ⁻¹' Iio (t : ℝ)) :=
      hcont.isOpen_preimage _ isOpen_Iio
    obtain ⟨delta, hdelta, hball⟩ :=
      Metric.isOpen_iff.mp hopen (i : ℝ) hlt
    have hterm : ∀ q : ℚ≥0, ENNReal.ofReal ((i : ℝ) + delta / 2) ≤
        (if (t : ℝ) < timeChangePathClock a theta omega (q : ℝ)
          then ENNReal.ofReal (q : ℝ) else ∞) := by
      intro q
      split_ifs with hcross
      · refine ENNReal.ofReal_le_ofReal ?_
        by_contra hq
        push_neg at hq
        rcases le_or_gt ((i : ℝ)) ((q : ℝ)) with hiq | hiq
        · have hmem : (q : ℝ) ∈ Metric.ball ((i : ℝ)) delta := by
            rw [Real.ball_eq_Ioo]
            constructor
            · linarith
            · linarith
          exact absurd (hball hmem) (not_lt.mpr hcross.le)
        · have : timeChangePathClock a theta omega (q : ℝ) ≤
              timeChangePathClock a theta omega (i : ℝ) := hmono hiq.le
          linarith
      · exact le_top
    have hinf : ENNReal.ofReal ((i : ℝ) + delta / 2) ≤
        timeChangeRationalInverse a theta t omega := le_iInf hterm
    have hcontra : ENNReal.ofReal ((i : ℝ) + delta / 2) ≤ (i : ℝ≥0∞) := hinf.trans hle
    rw [ENNReal.ofReal_le_iff_le_toReal (by simp), ENNReal.coe_toReal] at hcontra
    linarith
  · intro hti
    by_contra hle
    push_neg at hle
    obtain ⟨q, hqnonneg, hiq, hqinf⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hle
    let qn : ℚ≥0 := ⟨q, hqnonneg⟩
    have hqn : (Real.toNNReal q : NNReal) = (qn : NNReal) := by
      apply NNReal.eq
      rw [Real.coe_toNNReal', max_eq_left (Rat.cast_nonneg.mpr hqnonneg)]
      rfl
    have hiqNN : i < (qn : NNReal) := by
      rw [← hqn]
      exact ENNReal.coe_lt_coe.mp hiq
    have hiqreal : ((i : NNReal) : ℝ) < ((qn : NNReal) : ℝ) :=
      NNReal.coe_lt_coe.mpr hiqNN
    have hcoe : ((qn : NNReal) : ℝ) = ((qn : ℚ≥0) : ℝ) := rfl
    have hcross : (t : ℝ) < timeChangePathClock a theta omega ((qn : ℝ)) := by
      refine hti.trans_lt ?_
      rw [← hcoe]
      exact hstrict (Set.mem_Ici.mpr i.coe_nonneg)
        (Set.mem_Ici.mpr (le_of_lt (lt_of_le_of_lt i.coe_nonneg hiqreal))) hiqreal
    have hterm : timeChangeRationalInverse a theta t omega ≤
        ENNReal.ofReal ((qn : ℝ)) :=
      (iInf_le _ qn).trans_eq (if_pos hcross)
    have hqr : ((qn : ℚ≥0) : ℝ) = (q : ℝ) := rfl
    have hofReal : ENNReal.ofReal ((qn : ℝ)) = ((Real.toNNReal q : NNReal) : ℝ≥0∞) := by
      rw [hqr]
      rfl
    rw [hofReal] at hterm
    exact absurd (hterm.trans_lt hqinf) (lt_irrefl _)

/-- **The inverse intrinsic clock is a stopping time.**  This is the
hypothesis of the library's restart theorems at a stopping time; it is what a
Markov-property proof for the time-changed process consumes together with the
shift cocycle. -/
theorem isStoppingTime_timeChangeRationalInverse
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (t : NNReal) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := State d))
      (timeChangeRationalInverse a theta t) := by
  intro i
  have hmeas : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := State d) i]
      {omega : ContinuousPath (State d) |
        (t : ℝ) ≤ timeChangePathClock a theta omega (i : ℝ)} :=
    measurableSet_le measurable_const
      (measurable_timeChangePathClock_canonicalFiltration ha hapos default i)
  refine MeasurableSet.congr hmeas ?_
  ext omega
  exact (timeChangeRationalInverse_le_iff ha hapos t i omega).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
