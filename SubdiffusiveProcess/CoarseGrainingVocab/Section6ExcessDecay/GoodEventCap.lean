module

public import SubdiffusiveProcess.Section6.Defs.GoodEvent

@[expose] public section

/-!
# The good-event plumbing of the one-step estimate

Two bookkeeping moves of the printed proof of
`l.excess.decay.good.scales.GMC` concern the good event alone:

* **Step 2**, "since `ε ≤ 1`, the event `G_{n+2,z}(ε,s/8)` implies
  `G_{n+2,z}(1,s/8)`": the good event is monotone in its `ε` slot, which is what
  lets the harmonic-approximation input — stated at `ε = 1` — be applied on the
  smaller `ε`-event;
* **Step 7**, the passage from an inequality valid on the event to the
  indicator-valued inequality of the frozen conclusion.

Both are proved here from the frozen definitions.  The quantitative cap
`𝓔·1_G ≤ Cε` itself is *not* here: it is the second conclusion of
`p.good.scale.mathcal.E`, a separate anchor.

## References

* Proof steps `step.l.excess.decay.good.scales.SubdiffusiveProcess.2`, `.7` of the manuscript.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### Monotonicity of the good event in `ε` -/

theorem goodFieldOne_mono {m : ℕ} {y : Vec d} {epsilon epsilon' s : ℝ}
    (hee : epsilon ≤ epsilon')
    {ω : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (h : GoodFieldOne m y epsilon s ω) : GoodFieldOne m y epsilon' s ω := by
  intro j
  refine (h j).trans ?_
  exact mul_le_mul_of_nonneg_right hee (Real.rpow_nonneg (by norm_num) _)

theorem goodResponse_mono {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {cutoff : Option ℕ}
    {m : ℕ} {y : Vec d} {epsilon epsilon' s : ℝ} (he : 0 ≤ epsilon)
    (hee : epsilon ≤ epsilon') {ω : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (h : GoodResponse M cutoff m y epsilon s ω) :
    GoodResponse M cutoff m y epsilon' s ω := by
  intro j n hjm hnj w hgrid hshell e he1
  refine (h j n hjm hnj w hgrid hshell e he1).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _)
  exact pow_le_pow_left₀ he hee 2

/-- **The good event is monotone in `ε`.**  This is the step "since `ε ≤ 1`, the
event `G_{n+2,z}(ε,s/8)` implies `G_{n+2,z}(1,s/8)`". -/
theorem goodEvent_mono {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {cutoff : Option ℕ}
    {m : ℕ} {y : Vec d} {epsilon epsilon' s : ℝ} (he : 0 ≤ epsilon)
    (hee : epsilon ≤ epsilon') :
    goodEvent M cutoff m y epsilon s ⊆ goodEvent M cutoff m y epsilon' s := by
  rintro ω ⟨h1, h2, h3⟩
  exact ⟨goodFieldOne_mono hee h1, h2, goodResponse_mono he hee h3⟩

/-! ### The indicator convention -/

theorem indicatorValue_of_mem {Ω : Type*} {E : Set Ω} {X : Ω → ℝ} {ω : Ω} (hω : ω ∈ E) :
    indicatorValue E X ω = X ω := by
  rw [indicatorValue, ite_eq_left hω]

theorem indicatorValue_of_notMem {Ω : Type*} {E : Set Ω} {X : Ω → ℝ} {ω : Ω}
    (hω : ω ∉ E) : indicatorValue E X ω = 0 := by
  rw [indicatorValue, ite_eq_right hω]

/-- **The indicator packaging of a conditional estimate.**  An inequality that
holds at every point of the event, with a nonnegative right-hand side,
upgrades to the indicator-valued inequality of the frozen conclusions. -/
theorem indicatorValue_le {Ω : Type*} {E : Set Ω} {X : Ω → ℝ} {B : ℝ} {ω : Ω}
    (hB : 0 ≤ B) (h : ω ∈ E → X ω ≤ B) : indicatorValue E X ω ≤ B := by
  by_cases hω : ω ∈ E
  · rw [indicatorValue_of_mem hω]
    exact h hω
  · rw [indicatorValue_of_notMem hω]
    exact hB

/-- **Transport of an indicator estimate to a smaller event.**  The
harmonic-approximation input is stated on the `ε = 1` event; on the smaller
`ε`-event its indicator value is the same. -/
theorem indicatorValue_le_of_subset {Ω : Type*} {E E' : Set Ω} {X : Ω → ℝ} {B : ℝ}
    {ω : Ω} (hsub : E ⊆ E') (hB : 0 ≤ B) (h : indicatorValue E' X ω ≤ B) :
    indicatorValue E X ω ≤ B := by
  by_cases hω : ω ∈ E
  · rw [indicatorValue_of_mem hω]
    rw [indicatorValue_of_mem (hsub hω)] at h
    exact h
  · rw [indicatorValue_of_notMem hω]
    exact hB

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
