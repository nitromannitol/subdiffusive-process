import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### Monotonicity of the good event in `ε` -/

theorem goodFieldOne_mono {m : ℕ} {y : Vec d} {epsilon epsilon' s : ℝ}
    (hee : epsilon ≤ epsilon')
    {ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (h : GoodFieldOne m y epsilon s ω) : GoodFieldOne m y epsilon' s ω := by
  intro j
  refine (h j).trans ?_
  exact mul_le_mul_of_nonneg_right hee (Real.rpow_nonneg (by norm_num) _)

theorem goodResponse_mono {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {cutoff : Option ℕ}
    {m : ℕ} {y : Vec d} {epsilon epsilon' s : ℝ} (he : 0 ≤ epsilon)
    (hee : epsilon ≤ epsilon') {ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (h : GoodResponse M cutoff m y epsilon s ω) :
    GoodResponse M cutoff m y epsilon' s ω := by
  intro j n hjm hnj w hgrid hshell e he1
  refine (h j n hjm hnj w hgrid hshell e he1).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _)
  exact pow_le_pow_left₀ he hee 2

/-- **The good event is monotone in `ε`.**  This is the step "since `ε ≤ 1`, the
event `G_{n+2,z}(ε,s/8)` implies `G_{n+2,z}(1,s/8)`". -/
theorem goodEvent_mono {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {cutoff : Option ℕ}
    {m : ℕ} {y : Vec d} {epsilon epsilon' s : ℝ} (he : 0 ≤ epsilon)
    (hee : epsilon ≤ epsilon') :
    goodEvent M cutoff m y epsilon s ⊆ goodEvent M cutoff m y epsilon' s := by
  rintro ω ⟨h1, h2, h3⟩
  exact ⟨goodFieldOne_mono hee h1, h2, goodResponse_mono he hee h3⟩

/-! ### The indicator convention -/

theorem indicatorValue_of_mem {Ω : Type*} {E : Set Ω} {X : Ω → ℝ} {ω : Ω} (hω : ω ∈ E) :
    indicatorValue E X ω = X ω := by
  rw [indicatorValue, if_pos hω]

theorem indicatorValue_of_notMem {Ω : Type*} {E : Set Ω} {X : Ω → ℝ} {ω : Ω}
    (hω : ω ∉ E) : indicatorValue E X ω = 0 := by
  rw [indicatorValue, if_neg hω]

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
