import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalDistanceMeasurable
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalHeightTail




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-! ## The carrier -/



def chemicalComponentScale (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (Clen : ℝ)
    (z : Lattice d) (ω : Ω) : ℕ :=
  max 1 (sInf (chemicalDistanceHeightSet E Cbox Clen z ω))

omit [MeasurableSpace Ω] in
theorem one_le_chemicalComponentScale (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) (z : Lattice d) (ω : Ω) :
    1 ≤ chemicalComponentScale E Cbox Clen z ω :=
  le_max_left _ _

omit [MeasurableSpace Ω] in
theorem chemicalComponentScale_eq_height_sub (E : ℕ → Lattice d → Set Ω)
    (Cbox : ℕ) (Clen : ℝ) (z : Lattice d) (ω : Ω) :
    chemicalComponentScale E Cbox Clen z ω =
      max 1 (chemicalDistanceHeight E Cbox Clen z ω - 1) := by
  simp [chemicalComponentScale, chemicalDistanceHeight]

omit [MeasurableSpace Ω] in
/-- Above the scale there is no dyadic failure, provided some threshold works. -/
theorem not_mem_chemicalDistanceFailureEvent_of_chemicalComponentScale_le
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {z : Lattice d} {ω : Ω}
    (hne : (chemicalDistanceHeightSet E Cbox Clen z ω).Nonempty) {n : ℕ}
    (hn : chemicalComponentScale E Cbox Clen z ω ≤ n) :
    ω ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n) :=
  Nat.sInf_mem hne n (le_trans (le_max_right _ _) hn)

omit [MeasurableSpace Ω] in
/-- The tail inclusion.  Note the exponent range starts at `k`, not `k - 1`:
this is what the shift by one buys. -/
theorem chemicalComponentScale_gt_subset (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) (z : Lattice d) {k : ℕ} (hk : 1 ≤ k) :
    {ω : Ω | k < chemicalComponentScale E Cbox Clen z ω} ⊆
      ⋃ n ∈ {n : ℕ | k ≤ n}, chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n) := by
  intro ω hω
  simp only [mem_setOf_eq, chemicalComponentScale] at hω
  have hlt : k < sInf (chemicalDistanceHeightSet E Cbox Clen z ω) := by
    rcases max_cases 1 (sInf (chemicalDistanceHeightSet E Cbox Clen z ω)) with
      ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hnot : k ∉ chemicalDistanceHeightSet E Cbox Clen z ω := fun hmem =>
    absurd (Nat.sInf_le hmem) (not_le.mpr hlt)
  simp only [chemicalDistanceHeightSet, mem_setOf_eq, not_forall, not_not] at hnot
  obtain ⟨n, hkn, hmem⟩ := hnot
  exact mem_biUnion hkn hmem

theorem measurable_chemicalComponentScale {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {Clen : ℝ} {z : Lattice d}
    (hD : ∀ n : ℕ, MeasurableSet (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n))) :
    Measurable (chemicalComponentScale E Cbox Clen z) := by
  have h : chemicalComponentScale E Cbox Clen z =
      (fun n : ℕ => max 1 (n - 1)) ∘ chemicalDistanceHeight E Cbox Clen z := by
    funext ω
    exact chemicalComponentScale_eq_height_sub E Cbox Clen z ω
  rw [h]
  exact (measurable_of_countable _).comp (measurable_chemicalDistanceHeight hD)

/-! ## The dyadic rate -/

/-- The rate of the dyadic geometric tail: at `L = 2 ^ n` the printed bound
`Cfail exp (-c q (log L) ^ 2)` reads `Cfail exp (-(rate n ^ 2))` with
`rate = c q (log 2) ^ 2`, which is **linear in `q`**. -/
def chemicalTailRate (c q : ℝ) : ℝ := c * q * Real.log 2 ^ 2

theorem chemicalTailRate_pos {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    0 < chemicalTailRate c q := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : 0 < Real.log 2 ^ 2 := by positivity
  exact mul_pos (mul_pos hc hq) this

/-- The printed bound at a dyadic radius, in the rate normalisation. -/
theorem chemicalDyadic_bound_rewrite {c q Cfail : ℝ} (n : ℕ) :
    Cfail * Real.exp (-c * q * Real.log ((2 ^ n : ℕ) : ℝ) ^ 2) =
      Cfail * Real.exp (-(chemicalTailRate c q * (n : ℝ) ^ 2)) := by
  have hcast : (((2 : ℕ) ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  rw [hcast, Real.log_pow]
  congr 2
  rw [chemicalTailRate]
  ring

/-! ## The geometric tail of the scale -/

theorem measure_chemicalComponentScale_gt_le (mu : Measure Ω)
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen Cfail rate : ℝ} {z : Lattice d}
    (hCfail : 0 ≤ Cfail) (hrate : 0 < rate)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      mu (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) ≤
        ENNReal.ofReal (Cfail * Real.exp (-(rate * (n : ℝ) ^ 2))))
    {k : ℕ} (hk : 1 ≤ k) :
    mu {ω | k < chemicalComponentScale E Cbox Clen z ω} ≤
      ENNReal.ofReal (Cfail * Real.exp (-(rate * k)) / (1 - Real.exp (-rate))) := by
  refine le_trans (measure_mono (chemicalComponentScale_gt_subset E Cbox Clen z hk)) ?_
  refine measure_iUnion_ge_le_geometric mu _ hCfail hrate k ?_
  intro n hn
  refine (hbound n (le_trans hk hn)).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCfail
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hk hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  nlinarith [mul_nonneg (mul_nonneg hrate.le hn0) (by linarith : (0:ℝ) ≤ (n : ℝ) - 1)]



def chemicalTailPrefactor (Cfail rate : ℝ) : ℝ :=
  max 1 (Cfail / (1 - Real.exp (-rate)))

theorem one_le_chemicalTailPrefactor (Cfail rate : ℝ) :
    1 ≤ chemicalTailPrefactor Cfail rate := le_max_left _ _

/-- For `rate ≥ 1` the prefactor is at most `max 1 (2 Cfail)`, uniformly in the
rate — this is what keeps the final amplitude proportional to `1 / q`. -/
theorem chemicalTailPrefactor_le {Cfail rate : ℝ} (hCfail : 0 ≤ Cfail)
    (hrate : 1 ≤ rate) :
    chemicalTailPrefactor Cfail rate ≤ max 1 (2 * Cfail) := by
  have hexp : Real.exp (-rate) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have hlt : Real.exp (-1) < 1 / 2 := by
    have h2 : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [Real.exp_neg]
    rw [inv_lt_iff_one_lt_mul₀ hpos]
    nlinarith
  have hden : (1 : ℝ) / 2 ≤ 1 - Real.exp (-rate) := by linarith
  have hdenpos : (0 : ℝ) < 1 - Real.exp (-rate) := by linarith
  refine max_le (le_max_left _ _) (le_trans ?_ (le_max_right _ _))
  rw [div_le_iff₀ hdenpos]
  nlinarith

/-! ## The `O_{Γ₁}` bound with centre exactly `1` -/

/-- **P374-F5, settled.**  The dyadic bounds give
`chemicalComponentScale - 1 ≤ O_{Γ₁}(4 (1 + log K) / rate)`, with the centre the
literal `1` and no residual shift. -/
theorem ogammaLE_chemicalComponentScale (mu : Measure Ω) [IsProbabilityMeasure mu]
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen Cfail rate : ℝ} {z : Lattice d}
    (hD : ∀ n : ℕ, MeasurableSet (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)))
    (hCfail : 0 ≤ Cfail) (hrate : 0 < rate)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      mu (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) ≤
        ENNReal.ofReal (Cfail * Real.exp (-(rate * (n : ℝ) ^ 2)))) :
    SubdiffusiveProcess.OGammaLE mu 1
      (4 * ((1 + Real.log (chemicalTailPrefactor Cfail rate)) / rate))
      (fun ω => (chemicalComponentScale E Cbox Clen z ω : ℝ) - 1) := by
  have hK : 1 ≤ chemicalTailPrefactor Cfail rate := one_le_chemicalTailPrefactor _ _
  have hexplt : Real.exp (-rate) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hdenpos : (0 : ℝ) < 1 - Real.exp (-rate) := by linarith
  have htail : ∀ k : ℕ, 0 < k →
      mu.real {ω | k < chemicalComponentScale E Cbox Clen z ω} ≤
        chemicalTailPrefactor Cfail rate * Real.exp (-(rate * (k : ℝ))) := by
    intro k hk
    have hmeas := measure_chemicalComponentScale_gt_le mu hCfail hrate hbound hk
    have hnn : 0 ≤ Cfail * Real.exp (-(rate * k)) / (1 - Real.exp (-rate)) := by
      have : 0 ≤ Cfail * Real.exp (-(rate * k)) := by positivity
      positivity
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeas
    rw [ENNReal.toReal_ofReal hnn] at hreal
    refine le_trans hreal ?_
    have hle : Cfail / (1 - Real.exp (-rate)) ≤ chemicalTailPrefactor Cfail rate :=
      le_max_right _ _
    have heq : Cfail * Real.exp (-(rate * k)) / (1 - Real.exp (-rate)) =
        (Cfail / (1 - Real.exp (-rate))) * Real.exp (-(rate * k)) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
  have hbase := Section6CutoffRegularity.ogammaLE_one_depthObservable_sharp
    (μ := mu) (measurable_chemicalComponentScale hD) hK hrate htail
  have hobs : Section6CutoffRegularity.depthObservable
      (chemicalComponentScale E Cbox Clen z) =
      fun ω => (chemicalComponentScale E Cbox Clen z ω : ℝ) - 1 := by
    funext ω
    have h1 : (1 : ℝ) ≤ (chemicalComponentScale E Cbox Clen z ω : ℝ) := by
      exact_mod_cast one_le_chemicalComponentScale E Cbox Clen z ω
    simp only [Section6CutoffRegularity.depthObservable]
    exact max_eq_left (by linarith)
  rw [hobs] at hbase
  simpa [Section6CutoffRegularity.depthGammaOneScaleSharp,
    Section6CutoffRegularity.depthTailScaleSharp] using hbase

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
