module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalDRSConditions
public import Mathlib.Probability.Independence.ZeroOne

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## Elementary measure plumbing -/

/-- `A` is covered by `A ∩ B` together with `A \ B`. -/
theorem measure_le_measure_inter_add_sdiff_left [MeasurableSpace Ω] (mu : Measure Ω)
    (A B : Set Ω) : mu A ≤ mu (A ∩ B) + mu (A \ B) := by
  have h : A ⊆ (A ∩ B) ∪ (A \ B) := by
    intro x hx
    by_cases hb : x ∈ B
    · exact Or.inl ⟨hx, hb⟩
    · exact Or.inr ⟨hx, hb⟩
  exact (measure_mono h).trans (measure_union_le _ _)

/-- `B` is covered by `A ∩ B` together with `B \ A`. -/
theorem measure_le_measure_inter_add_sdiff_right [MeasurableSpace Ω] (mu : Measure Ω)
    (A B : Set Ω) : mu B ≤ mu (A ∩ B) + mu (B \ A) := by
  have h : B ⊆ (A ∩ B) ∪ (B \ A) := by
    intro x hx
    by_cases ha : x ∈ A
    · exact Or.inl ⟨ha, hx⟩
    · exact Or.inr ⟨hx, ha⟩
  exact (measure_mono h).trans (measure_union_le _ _)

/-- Both `A` and `B` are within `e` of `A ∩ B` in probability once the symmetric difference
has measure at most `e`. -/
theorem abs_toReal_sub_toReal_inter_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (A B : Set Ω) {e : ℝ≥0∞} (he : e ≠ ⊤)
    (hAB : mu (A \ B) + mu (B \ A) ≤ e) :
    |(mu A).toReal - (mu (A ∩ B)).toReal| ≤ e.toReal ∧
      |(mu B).toReal - (mu (A ∩ B)).toReal| ≤ e.toReal := by
  have hIA : mu (A ∩ B) ≤ mu A := measure_mono Set.inter_subset_left
  have hIB : mu (A ∩ B) ≤ mu B := measure_mono Set.inter_subset_right
  have hdA : mu (A \ B) ≤ e := le_trans le_self_add hAB
  have hdB : mu (B \ A) ≤ e := le_trans le_add_self hAB
  have hI : mu (A ∩ B) ≠ ⊤ := measure_ne_top mu _
  have hAt : mu A ≠ ⊤ := measure_ne_top mu _
  have hBt : mu B ≠ ⊤ := measure_ne_top mu _
  have hsum : mu (A ∩ B) + e ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hI, he⟩
  have hA : mu A ≤ mu (A ∩ B) + e :=
    (measure_le_measure_inter_add_sdiff_left mu A B).trans (add_le_add le_rfl hdA)
  have hB : mu B ≤ mu (A ∩ B) + e :=
    (measure_le_measure_inter_add_sdiff_right mu A B).trans (add_le_add le_rfl hdB)
  have hAr : (mu A).toReal ≤ (mu (A ∩ B)).toReal + e.toReal := by
    have := ENNReal.toReal_mono hsum hA
    rwa [ENNReal.toReal_add hI he] at this
  have hBr : (mu B).toReal ≤ (mu (A ∩ B)).toReal + e.toReal := by
    have := ENNReal.toReal_mono hsum hB
    rwa [ENNReal.toReal_add hI he] at this
  have hIAr : (mu (A ∩ B)).toReal ≤ (mu A).toReal := ENNReal.toReal_mono hAt hIA
  have hIBr : (mu (A ∩ B)).toReal ≤ (mu B).toReal := ENNReal.toReal_mono hBt hIB
  have he0 : (0 : ℝ) ≤ e.toReal := ENNReal.toReal_nonneg
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-! ## The approximation form of the 0–1 law -/

/-- The event `A` can be approximated, in measure and to arbitrary accuracy, by events
independent of it. -/
def ApproximableByIndependent [MeasurableSpace Ω] (mu : Measure Ω) (A : Set Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : Set Ω,
    mu (A \ B) + mu (B \ A) ≤ ENNReal.ofReal ε ∧ mu (A ∩ B) = mu A * mu B

/-- A real number within `2 ε` of its own square for every `ε > 0` equals its square. -/
theorem eq_sq_of_forall_pos_abs_sub_le {a : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → |a - a * a| ≤ 2 * ε) : a = a * a := by
  have h0 : |a - a * a| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := h (ε / 2) (by linarith)
    linarith
  rw [abs_nonpos_iff] at h0
  exact sub_eq_zero.mp h0

/-- An idempotent real is `0` or `1`. -/
theorem eq_zero_or_one_of_eq_sq {a : ℝ} (h : a = a * a) : a = 0 ∨ a = 1 := by
  have hmul : a * (1 - a) = 0 := by nlinarith
  rcases mul_eq_zero.mp hmul with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by linarith)

/-- **The 0–1 law, approximation form.**  An event approximable by events independent of it
has probability `0` or `1`.  Mathlib's `measure_eq_zero_or_one_of_indepSet_self` is the
special case `B = A`. -/
theorem measure_eq_zero_or_one_of_approx_indep [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {A : Set Ω} (h : ApproximableByIndependent mu A) :
    mu A = 0 ∨ mu A = 1 := by
  have hle : (mu A).toReal ≤ 1 := by
    have := prob_le_one (μ := mu) (s := A)
    simpa using ENNReal.toReal_mono (by simp) this
  have h0 : (0 : ℝ) ≤ (mu A).toReal := ENNReal.toReal_nonneg
  have key : (mu A).toReal = (mu A).toReal * (mu A).toReal := by
    refine eq_sq_of_forall_pos_abs_sub_le fun ε hε => ?_
    obtain ⟨B, hsym, hindep⟩ := h (ε / 2) (by linarith)
    have hne : ENNReal.ofReal (ε / 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    obtain ⟨h1, h2⟩ := abs_toReal_sub_toReal_inter_le mu A B hne hsym
    rw [ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ ε / 2)] at h1 h2
    have hp : (mu (A ∩ B)).toReal = (mu A).toReal * (mu B).toReal := by
      rw [hindep, ENNReal.toReal_mul]
    rw [hp] at h1 h2
    have hab : |(mu A).toReal - (mu B).toReal| ≤ ε := by
      have := abs_sub_abs_le_abs_sub ((mu A).toReal) ((mu B).toReal)
      have hstep : |(mu A).toReal - (mu B).toReal| ≤
          |(mu A).toReal - (mu A).toReal * (mu B).toReal| +
            |(mu A).toReal * (mu B).toReal - (mu B).toReal| := abs_sub_le _ _ _
      have h2' : |(mu A).toReal * (mu B).toReal - (mu B).toReal| ≤ ε / 2 := by
        rw [abs_sub_comm]; exact h2
      linarith
    have hsplit : |(mu A).toReal - (mu A).toReal * (mu A).toReal| ≤
        |(mu A).toReal - (mu A).toReal * (mu B).toReal| +
          |(mu A).toReal * (mu B).toReal - (mu A).toReal * (mu A).toReal| :=
      abs_sub_le _ _ _
    have hfac : |(mu A).toReal * (mu B).toReal - (mu A).toReal * (mu A).toReal| ≤ ε := by
      have : (mu A).toReal * (mu B).toReal - (mu A).toReal * (mu A).toReal =
          (mu A).toReal * ((mu B).toReal - (mu A).toReal) := by ring
      rw [this, abs_mul, abs_of_nonneg h0, abs_sub_comm]
      nlinarith [abs_nonneg ((mu A).toReal - (mu B).toReal)]
    linarith
  rcases eq_zero_or_one_of_eq_sq key with hz | ho
  · exact Or.inl (((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top mu A))
  · refine Or.inr ?_
    have := (ENNReal.toReal_eq_one_iff (mu A)).mp ho
    exact this

/-! ## The configuration law is a probability measure -/

/-- The configuration map is measurable once every event is. -/
theorem measurable_eventFieldConfiguration [MeasurableSpace Ω] {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) :
    Measurable (eventFieldConfiguration E) := by
  refine measurable_pi_iff.mpr fun p => ?_
  exact measurable_const.indicator (hE p.1 p.2)

/-- The configuration law of a translation-invariant event field is a probability measure. -/
theorem isProbabilityMeasure_map_eventFieldConfiguration [MeasurableSpace Ω]
    {mu : Measure Ω} [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω}
    (hlaw : TranslationInvariantEventLaw mu E) :
    IsProbabilityMeasure (Measure.map (eventFieldConfiguration E) mu) :=
  by infer_instance

/-! ## P1 from asymptotic independence -/

/-- **`[DRS]` condition P1 from asymptotic independence.**  Translation invariance of the
configuration law, together with the approximation datum for every measurable shift-invariant
event, is exactly P1.

The approximation datum is the residual recorded in the module docstring: it is what the
manuscript's finite-range decoupling supplies, and it carries no percolation content. -/
theorem drsConditionP1_of_approximableByIndependent [MeasurableSpace Ω] {mu : Measure Ω}
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω}
    (hlaw : TranslationInvariantEventLaw mu E)
    (happrox : ∀ A : Set (ℕ × Lattice d → ℝ), MeasurableSet A →
      (∀ a : Lattice d, configShift a ⁻¹' A = A) →
      ApproximableByIndependent (Measure.map (eventFieldConfiguration E) mu) A) :
    DRSConditionP1 mu E := by
  haveI : IsProbabilityMeasure (Measure.map (eventFieldConfiguration E) mu) :=
    isProbabilityMeasure_map_eventFieldConfiguration hlaw
  exact ⟨hlaw, fun A hA hinv =>
    measure_eq_zero_or_one_of_approx_indep _ (happrox A hA hinv)⟩

/-! ## What Kolmogorov's 0–1 law gives instead -/

/-- **Kolmogorov's 0–1 law for the scale family.**  Every event in the tail σ-algebra of the
independent scale fields is trivial.

This is *not* P1: a spatially shift-invariant event need not be a scale-tail event (see the
module docstring).  It is, however, exactly the triviality of the "influence from arbitrarily
high levels" σ-algebra that the truncation argument of
`Section9ChemicalDRSConditions.measure_highLevelInfluence_le_tsum` quantifies. -/
theorem measure_eq_zero_or_one_of_scaleTail [MeasurableSpace Ω] {mu : Measure Ω}
    {E : ℕ → Lattice d → Set Ω} (hE : ∀ j z, MeasurableSet (E j z))
    (hscales : IndependentEventScales mu E) {t : Set Ω}
    (ht : MeasurableSet[Filter.limsup (fun j => eventFieldSigma (E j) Set.univ) Filter.atTop] t) :
    mu t = 0 ∨ mu t = 1 := by
  refine ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop ?_ hscales ht
  intro j
  refine MeasurableSpace.generateFrom_le ?_
  rintro A ⟨z, -, rfl⟩
  exact hE j z

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
