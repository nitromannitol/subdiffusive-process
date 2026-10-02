import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalDistance
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingTailGeometric




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Summation of a geometric bound over a tail of indices, for arbitrary (not
necessarily measurable) sets. -/
theorem measure_iUnion_ge_le_geometric (mu : Measure Ω) (D : ℕ → Set Ω)
    {Cf r : ℝ} (hCf : 0 ≤ Cf) (hr : 0 < r) (h : ℕ)
    (hbound : ∀ n : ℕ, h ≤ n → mu (D n) ≤ ENNReal.ofReal (Cf * Real.exp (-(r * n)))) :
    mu (⋃ n ∈ {n : ℕ | h ≤ n}, D n) ≤
      ENNReal.ofReal (Cf * Real.exp (-(r * h)) / (1 - Real.exp (-r))) := by
  have hlt1 : Real.exp (-r) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnn : (0 : ℝ) ≤ Real.exp (-r) := (Real.exp_pos _).le
  have hreindex : (⋃ n ∈ {n : ℕ | h ≤ n}, D n) = ⋃ k : ℕ, D (h + k) := by
    ext x
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨n, hn, hx⟩
      exact ⟨n - h, by rwa [Nat.add_sub_cancel' hn]⟩
    · rintro ⟨k, hx⟩
      exact ⟨h + k, Nat.le_add_right _ _, hx⟩
  rw [hreindex]
  refine le_trans (measure_iUnion_le _) ?_
  have hterm : ∀ k : ℕ,
      mu (D (h + k)) ≤
        ENNReal.ofReal (Cf * Real.exp (-(r * h)) * Real.exp (-r) ^ k) := by
    intro k
    refine (hbound (h + k) (Nat.le_add_right h k)).trans ?_
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hexp : Real.exp (-(r * h)) * Real.exp (-r) ^ k =
        Real.exp (-(r * ((h : ℝ) + k))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, hexp]
    push_cast
    ring
  have hsummable : Summable fun k : ℕ =>
      Cf * Real.exp (-(r * h)) * Real.exp (-r) ^ k :=
    (summable_geometric_of_lt_one hnn hlt1).mul_left _
  have hnonneg : ∀ k : ℕ, 0 ≤ Cf * Real.exp (-(r * h)) * Real.exp (-r) ^ k := by
    intro k
    have : (0 : ℝ) ≤ Cf * Real.exp (-(r * h)) := by positivity
    positivity
  calc ∑' k : ℕ, mu (D (h + k))
      ≤ ∑' k : ℕ, ENNReal.ofReal (Cf * Real.exp (-(r * h)) * Real.exp (-r) ^ k) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' k : ℕ, Cf * Real.exp (-(r * h)) * Real.exp (-r) ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable).symm
    _ = ENNReal.ofReal (Cf * Real.exp (-(r * h)) / (1 - Real.exp (-r))) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hnn hlt1, div_eq_mul_inv]

/-- **`P[H₂(z) > h] ≤ C e^{-c q h}`.**  The dyadic bounds
`P[D_{2^n}(z)] ≤ Cfail exp (-(rate n ^ 2))` sum to a geometric tail of the
height, because `n ^ 2 ≥ n`. -/
theorem measure_chemicalDistanceHeight_gt_le (mu : Measure Ω)
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen Cfail rate : ℝ} {z : Lattice d}
    (hCfail : 0 ≤ Cfail) (hrate : 0 < rate)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      mu (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) ≤
        ENNReal.ofReal (Cfail * Real.exp (-(rate * (n : ℝ) ^ 2))))
    {h : ℕ} (hh : 1 ≤ h) :
    mu {ω | h + 1 < chemicalDistanceHeight E Cbox Clen z ω} ≤
      ENNReal.ofReal (Cfail * Real.exp (-(rate * h)) / (1 - Real.exp (-rate))) := by
  refine le_trans (measure_mono (chemicalDistanceHeight_gt_subset E Cbox Clen z h)) ?_
  refine measure_iUnion_ge_le_geometric mu _ hCfail hrate h ?_
  intro n hn
  refine (hbound n (le_trans hh hn)).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCfail
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hh hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  nlinarith [mul_nonneg (mul_nonneg hrate.le hn0) (by linarith : (0:ℝ) ≤ (n : ℝ) - 1)]

/-- At `σ = 1` the `O_{Γ_1}` convention is exactly homogeneous: rescaling the
observable rescales the amplitude. -/
theorem ogammaLE_one_rescale {mu : Measure Ω} {A s c : ℝ} (hs : 0 < s)
    {X : Ω → ℝ} (h : SubdiffusiveProcess.OGammaLE mu 1 A (fun omega => X omega * s - c)) :
    SubdiffusiveProcess.OGammaLE mu 1 (A / s) (fun omega => X omega - c / s) := by
  unfold SubdiffusiveProcess.OGammaLE at h ⊢
  have key : ∀ ω, ((A / s)⁻¹ * max (X ω - c / s) 0) = A⁻¹ * max (X ω * s - c) 0 := by
    intro ω
    have hs0 : 0 ≤ s := le_of_lt hs
    have he : X ω * s - c = s * (X ω - c / s) := by field_simp
    have hm : max (s * (X ω - c / s)) 0 = s * max (X ω - c / s) 0 := by
      rcases le_or_gt 0 (X ω - c / s) with hle | hlt
      · rw [max_eq_left hle, max_eq_left (mul_nonneg hs0 hle)]
      · rw [max_eq_right (le_of_lt hlt),
          max_eq_right (mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_lt hlt)), mul_zero]
    rw [he, hm, div_eq_inv_mul, mul_inv, inv_inv]
    ring
  constructor
  · simp only [key]
    exact h.1
  · simp only [key]
    exact h.2

/-- The shift which turns the height tail into the `C * theta ^ k` shape. -/
theorem ofReal_exp_shift_eq {Cg r : ℝ} (hCg : 0 ≤ Cg) (h : ℕ) :
    ENNReal.ofReal (Cg * Real.exp (-(r * h))) =
      ENNReal.ofReal (Cg * Real.exp (2 * r)) *
        ENNReal.ofReal (Real.exp (-r)) ^ (h + 2) := by
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hexp : Real.exp (-r) ^ (h + 2) = Real.exp ((h + 2 : ℕ) * -r) := by
    rw [Real.exp_nat_mul]
  rw [mul_assoc, hexp, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem stoppingTailRate_ofReal_exp_neg {r : ℝ} :
    Section8Resolvent.stoppingTailRate (ENNReal.ofReal (Real.exp (-r))) = r := by
  rw [Section8Resolvent.stoppingTailRate,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.exp_neg, inv_inv, Real.log_exp]



theorem exists_ogammaLE_chemicalDistanceHeight (mu : Measure Ω)
    [IsProbabilityMeasure mu]
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen Cfail rate : ℝ} {z : Lattice d}
    (hmeas : Measurable (chemicalDistanceHeight E Cbox Clen z))
    (hCfail : 0 ≤ Cfail) (hrate : 0 < rate)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      mu (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) ≤
        ENNReal.ofReal (Cfail * Real.exp (-(rate * (n : ℝ) ^ 2)))) :
    ∃ centre : ℝ, SubdiffusiveProcess.OGammaLE mu 1 (4 / rate)
      (fun omega => (chemicalDistanceHeight E Cbox Clen z omega : ℝ) - centre) := by
  set theta : ENNReal := ENNReal.ofReal (Real.exp (-rate)) with htheta
  have hexpltone : Real.exp (-rate) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hthetapos : 0 < theta := by
    rw [htheta]
    simpa using Real.exp_pos (-rate)
  have hthetalt : theta < 1 := by
    rw [htheta, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hexpltone
  set Cg : ℝ := Cfail / (1 - Real.exp (-rate)) with hCg
  have hCgnn : 0 ≤ Cg := by
    rw [hCg]
    have : 0 < 1 - Real.exp (-rate) := by linarith
    positivity
  set Ctail : ENNReal := ENNReal.ofReal (Cg * Real.exp (2 * rate)) with hCtail
  have htail : ∀ k : ℕ, 3 ≤ k →
      mu {omega | k ≤ chemicalDistanceHeight E Cbox Clen z omega} ≤ Ctail * theta ^ k := by
    intro k hk
    obtain ⟨h, rfl⟩ : ∃ h : ℕ, k = h + 2 := ⟨k - 2, by omega⟩
    have hh : 1 ≤ h := by omega
    have hset : {omega | h + 2 ≤ chemicalDistanceHeight E Cbox Clen z omega} =
        {omega | h + 1 < chemicalDistanceHeight E Cbox Clen z omega} := by
      ext omega
      simp only [mem_setOf_eq]
      omega
    rw [hset, hCtail, htheta, ← ofReal_exp_shift_eq hCgnn h]
    have := measure_chemicalDistanceHeight_gt_le mu hCfail hrate hbound hh
    refine this.trans (le_of_eq ?_)
    rw [hCg]
    congr 1
    ring
  have hbridge := Section8Resolvent.ogammaLE_of_geometric_tail (mu := mu)
    hmeas (C := Ctail) (theta := theta) (by simp [hCtail]) hthetapos hthetalt 3 htail
  rw [stoppingTailRate_ofReal_exp_neg] at hbridge
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hrescale := ogammaLE_one_rescale (mu := mu) hlog3 hbridge
  have hamp : Section8Resolvent.stoppingTailGammaOneConstant * Real.log 3 / rate /
      Real.log 3 = 4 / rate := by
    rw [Section8Resolvent.stoppingTailGammaOneConstant]
    field_simp
  rw [hamp] at hrescale
  exact ⟨_, hrescale⟩

/-! ## Measurability of the height (`M7`)

`chemicalDistanceHeight` is the `+1` shift of the least element of the
upward-closed set `chemicalDistanceHeightSet`.  Since that set is upward closed,
`sInf` takes the value `j` exactly on `{j ∈ S} \ ⋃_{i < j} {i ∈ S}`, and the
empty-set branch contributes the `limsup` of the failure events; all three are
measurable as soon as every dyadic failure event is.  This discharges the
hypothesis `hmeas` of `exists_ogammaLE_chemicalDistanceHeight`. -/

theorem measurableSet_mem_chemicalDistanceHeightSet
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {z : Lattice d}
    (hD : ∀ n : ℕ, MeasurableSet (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)))
    (h : ℕ) :
    MeasurableSet {ω | h ∈ chemicalDistanceHeightSet E Cbox Clen z ω} := by
  have eq : {ω | h ∈ chemicalDistanceHeightSet E Cbox Clen z ω}
      = (⋃ n ∈ {n : ℕ | h ≤ n}, chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n))ᶜ := by
    ext ω
    simp [chemicalDistanceHeightSet]
  rw [eq]
  exact MeasurableSet.compl (MeasurableSet.biUnion (Set.to_countable _) fun n _ => hD n)

theorem measurable_chemicalDistanceHeight
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {z : Lattice d}
    (hD : ∀ n : ℕ, MeasurableSet (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n))) :
    Measurable (chemicalDistanceHeight E Cbox Clen z) := by
  have hm : ∀ i : ℕ, MeasurableSet {ω | i ∈ chemicalDistanceHeightSet E Cbox Clen z ω} :=
    fun i => measurableSet_mem_chemicalDistanceHeightSet hD i
  have sInf_empty : ∀ S : Set ℕ, S = ∅ → sInf S = 0 := by
    intro S hS
    subst hS
    exact Nat.sInf_eq_zero.2 (by simp)
  have hempty : MeasurableSet {ω | chemicalDistanceHeightSet E Cbox Clen z ω = ∅} := by
    have eq : {ω | chemicalDistanceHeightSet E Cbox Clen z ω = ∅}
        = ⋂ h : ℕ, ⋃ n ∈ {n : ℕ | h ≤ n},
            chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
      constructor
      · intro hs h
        by_contra hc
        push_neg at hc
        exact (Set.eq_empty_iff_forall_notMem.mp hs) h hc
      · intro hω
        rw [Set.eq_empty_iff_forall_notMem]
        intro h hh
        obtain ⟨n, hn, hf⟩ := hω h
        exact hh n hn hf
    rw [eq]
    exact MeasurableSet.iInter fun h =>
      MeasurableSet.biUnion (Set.to_countable _) fun n _ => hD n
  refine measurable_to_countable' fun m => ?_
  show MeasurableSet {ω | chemicalDistanceHeight E Cbox Clen z ω = m}
  rcases m with _ | j
  · have e0 : {ω | chemicalDistanceHeight E Cbox Clen z ω = 0} = ∅ := by
      ext ω
      constructor
      · intro hh
        simp only [Set.mem_setOf_eq, chemicalDistanceHeight] at hh
        omega
      · intro hh
        exact (hh : False).elim
    rw [e0]
    exact MeasurableSet.empty
  · rcases j with _ | k
    · have key : {ω | chemicalDistanceHeight E Cbox Clen z ω = 1}
        = {ω | 0 ∈ chemicalDistanceHeightSet E Cbox Clen z ω}
          ∪ {ω | chemicalDistanceHeightSet E Cbox Clen z ω = ∅} := by
        ext ω
        simp only [chemicalDistanceHeight, Set.mem_union, Set.mem_setOf_eq]
        constructor
        · intro h
          have hs : sInf (chemicalDistanceHeightSet E Cbox Clen z ω) = 0 := by omega
          by_cases hE : chemicalDistanceHeightSet E Cbox Clen z ω = ∅
          · exact Or.inr hE
          · left
            have hsinf := Nat.sInf_mem (Set.nonempty_iff_ne_empty.2 hE)
            rw [hs] at hsinf
            exact hsinf
        · rintro (h0 | hE)
          · have hle : sInf (chemicalDistanceHeightSet E Cbox Clen z ω) ≤ 0 :=
              Nat.sInf_le h0
            omega
          · rw [sInf_empty _ hE]
      rw [key]
      exact (hm 0).union hempty
    · have key : {ω | chemicalDistanceHeight E Cbox Clen z ω = k + 1 + 1}
        = {ω | k + 1 ∈ chemicalDistanceHeightSet E Cbox Clen z ω}
          \ ⋃ i ∈ {i : ℕ | i < k + 1}, {ω | i ∈ chemicalDistanceHeightSet E Cbox Clen z ω} := by
        ext ω
        simp only [chemicalDistanceHeight, Set.mem_diff, Set.mem_iUnion, Set.mem_setOf_eq]
        constructor
        · intro h
          have hs : sInf (chemicalDistanceHeightSet E Cbox Clen z ω) = k + 1 := by omega
          have hne : chemicalDistanceHeightSet E Cbox Clen z ω ≠ ∅ := by
            intro hE
            rw [sInf_empty _ hE] at hs
            omega
          have hmem : k + 1 ∈ chemicalDistanceHeightSet E Cbox Clen z ω := by
            have hsinf := Nat.sInf_mem (Set.nonempty_iff_ne_empty.2 hne)
            rw [hs] at hsinf
            exact hsinf
          refine ⟨hmem, ?_⟩
          intro hex
          obtain ⟨i, hi, himem⟩ := hex
          have hle := Nat.sInf_le himem
          omega
        · rintro ⟨hmem, hex⟩
          have hle : sInf (chemicalDistanceHeightSet E Cbox Clen z ω) ≤ k + 1 :=
            Nat.sInf_le hmem
          have hge : k + 1 ≤ sInf (chemicalDistanceHeightSet E Cbox Clen z ω) := by
            by_contra hc
            push_neg at hc
            have hsinf : sInf (chemicalDistanceHeightSet E Cbox Clen z ω)
                ∈ chemicalDistanceHeightSet E Cbox Clen z ω :=
              Nat.sInf_mem ⟨k + 1, hmem⟩
            exact hex ⟨sInf (chemicalDistanceHeightSet E Cbox Clen z ω), hc, hsinf⟩
          omega
      rw [key]
      exact (hm (k + 1)).diff (MeasurableSet.biUnion (Set.to_countable _) fun i _ => hm i)

/-- **The `H₂` tail with the measurability hypothesis discharged.**  Combining
`measurable_chemicalDistanceHeight` with
`exists_ogammaLE_chemicalDistanceHeight`: only measurability of the dyadic
failure events is needed. -/
theorem exists_ogammaLE_chemicalDistanceHeight_of_measurableEvents (mu : Measure Ω)
    [IsProbabilityMeasure mu]
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen Cfail rate : ℝ} {z : Lattice d}
    (hD : ∀ n : ℕ, MeasurableSet (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)))
    (hCfail : 0 ≤ Cfail) (hrate : 0 < rate)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      mu (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) ≤
        ENNReal.ofReal (Cfail * Real.exp (-(rate * (n : ℝ) ^ 2)))) :
    ∃ centre : ℝ, SubdiffusiveProcess.OGammaLE mu 1 (4 / rate)
      (fun omega => (chemicalDistanceHeight E Cbox Clen z omega : ℝ) - centre) :=
  exists_ogammaLE_chemicalDistanceHeight mu (measurable_chemicalDistanceHeight hD)
    hCfail hrate hbound

/-! ## Borel--Cantelli: the height is a.e. finite (`M7`)

The dyadic bounds are summable, so the event that *no* threshold works — i.e.
that `D_{2^n}(z)` occurs for arbitrarily large `n` — is null.  Hence almost
surely `chemicalDistanceHeightSet` is nonempty and the dyadic-threshold
hypothesis of `finiteRangePercolationGeometry_of_chemicalDistanceThresholds`
holds above `chemicalDistanceHeight`. -/

theorem measure_eq_zero_of_le_geometric (mu : Measure Ω) (T : Set Ω)
    {Cf r : ℝ} (hr : 0 < r)
    (hle : ∀ h : ℕ, mu T ≤ ENNReal.ofReal (Cf * Real.exp (-(r * h)) / (1 - Real.exp (-r)))) :
    mu T = 0 := by
  refine le_antisymm ?_ (zero_le _)
  set f : ℕ → ℝ≥0∞ :=
    fun h => ENNReal.ofReal (Cf * Real.exp (-(r * h)) / (1 - Real.exp (-r))) with hf
  have hexp : Filter.Tendsto (fun h : ℕ => Real.exp (-(r * (h : ℝ)))) Filter.atTop (nhds 0) := by
    have hlin : Filter.Tendsto (fun h : ℕ => -(r * (h : ℝ))) Filter.atTop Filter.atBot := by
      have h0 : Filter.Tendsto (fun h : ℕ => (h : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop
      exact Filter.tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hr h0)
    exact Real.tendsto_exp_atBot.comp hlin
  have hreal : Filter.Tendsto (fun h : ℕ => Cf * Real.exp (-(r * (h : ℝ))) / (1 - Real.exp (-r)))
      Filter.atTop (nhds 0) := by
    simpa using (hexp.const_mul Cf).div_const (1 - Real.exp (-r))
  have hE : Filter.Tendsto f Filter.atTop (nhds 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  exact ge_of_tendsto hE (Filter.Eventually.of_forall hle)

omit [MeasurableSpace Ω] in
theorem chemicalDistanceHeightSet_empty_subset (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) (z : Lattice d) (h : ℕ) :
    {ω | chemicalDistanceHeightSet E Cbox Clen z ω = ∅} ⊆
      ⋃ n ∈ {n : ℕ | h ≤ n}, chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n) := by
  intro ω hω
  simp only [mem_setOf_eq, Set.eq_empty_iff_forall_notMem] at hω
  have := hω h
  simp only [chemicalDistanceHeightSet, mem_setOf_eq, not_forall, not_not] at this
  obtain ⟨n, hn, hmem⟩ := this
  exact mem_biUnion hn hmem

theorem measure_chemicalDistanceHeightSet_empty_eq_zero (mu : Measure Ω)
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen Cfail rate : ℝ} {z : Lattice d}
    (hCfail : 0 ≤ Cfail) (hrate : 0 < rate)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      mu (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) ≤
        ENNReal.ofReal (Cfail * Real.exp (-(rate * (n : ℝ) ^ 2)))) :
    mu {ω | chemicalDistanceHeightSet E Cbox Clen z ω = ∅} = 0 := by
  refine measure_eq_zero_of_le_geometric mu _ (Cf := Cfail) hrate fun h => ?_
  refine le_trans (measure_mono (chemicalDistanceHeightSet_empty_subset E Cbox Clen z (h + 1))) ?_
  refine le_trans (measure_iUnion_ge_le_geometric mu _ hCfail hrate (h + 1) ?_) ?_
  · intro n hn
    have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 h) hn
    refine (hbound n hn1).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCfail
    have hc : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    nlinarith [mul_nonneg (mul_nonneg hrate.le (by linarith : (0:ℝ) ≤ (n:ℝ)))
      (by linarith : (0:ℝ) ≤ (n : ℝ) - 1)]
  · refine ENNReal.ofReal_le_ofReal ?_
    have hpos : 0 < 1 - Real.exp (-rate) := by
      have : Real.exp (-rate) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hexple : Real.exp (-(rate * ((h + 1 : ℕ) : ℝ))) ≤ Real.exp (-(rate * (h : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      push_cast
      nlinarith
    gcongr

/-- Almost surely some dyadic threshold works, so `H₂(z)` is the genuine
`1 + sup {n : D_{2^n}(z) occurs}`. -/
theorem ae_nonempty_chemicalDistanceHeightSet (mu : Measure Ω)
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen Cfail rate : ℝ} {z : Lattice d}
    (hCfail : 0 ≤ Cfail) (hrate : 0 < rate)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      mu (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) ≤
        ENNReal.ofReal (Cfail * Real.exp (-(rate * (n : ℝ) ^ 2)))) :
    ∀ᵐ ω ∂mu, (chemicalDistanceHeightSet E Cbox Clen z ω).Nonempty := by
  rw [MeasureTheory.ae_iff]
  have hset : {ω | ¬ (chemicalDistanceHeightSet E Cbox Clen z ω).Nonempty} =
      {ω | chemicalDistanceHeightSet E Cbox Clen z ω = ∅} := by
    ext ω
    simp [Set.not_nonempty_iff_eq_empty]
  rw [hset]
  exact measure_chemicalDistanceHeightSet_empty_eq_zero mu hCfail hrate hbound

/-- **The a.e. dyadic-threshold hypothesis.**  This is exactly the input
`hheight` of `finiteRangePercolationGeometry_of_chemicalDistanceThresholds`,
supplied almost surely by the summable dyadic bounds. -/
theorem ae_not_mem_chemicalDistanceFailureEvent (mu : Measure Ω)
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen Cfail rate : ℝ} {z : Lattice d}
    (hCfail : 0 ≤ Cfail) (hrate : 0 < rate)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      mu (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) ≤
        ENNReal.ofReal (Cfail * Real.exp (-(rate * (n : ℝ) ^ 2)))) :
    ∀ᵐ ω ∂mu, ∀ n : ℕ, chemicalDistanceHeight E Cbox Clen z ω ≤ n →
      ω ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n) :=
  (ae_nonempty_chemicalDistanceHeightSet mu hCfail hrate hbound).mono fun _ hω _ hn =>
    not_mem_chemicalDistanceFailureEvent_of_chemicalDistanceHeight_le hω hn

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
