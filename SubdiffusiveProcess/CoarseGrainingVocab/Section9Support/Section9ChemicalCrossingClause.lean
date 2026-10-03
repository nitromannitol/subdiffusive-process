module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalHeightTail

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Ω : Type*}

/-! ## The minimal scale -/

/-- The deterministic base scale of the crossing clause. -/
def crossL0 (Cbox J : ℕ) : ℕ := 12 * Cbox + 24 * J + 25

theorem one_le_crossL0 (Cbox J : ℕ) : 1 ≤ crossL0 Cbox J := by
  rw [crossL0]; omega

/-- The event that some crossing at a scale `≥ crossL0 + h` fails. -/
def crossFailUnion (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (z : Lattice d)
    (h : ℕ) : Set Ω :=
  ⋃ l : ℕ, ⋃ _ : crossL0 Cbox J + h ≤ l,
    crossFailEvent E Cbox J z l (crossCount J l)

theorem crossFailUnion_antitone (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ)
    (z : Lattice d) {h h' : ℕ} (hle : h ≤ h') :
    crossFailUnion E Cbox J z h' ⊆ crossFailUnion E Cbox J z h := by
  intro ω hω
  obtain ⟨l, hl, hmem⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨l, by omega, hmem⟩

theorem measurableSet_crossFailUnion [MeasurableSpace Ω]
    {E : ℕ → Lattice d → Set Ω} (hE : ∀ j z, MeasurableSet (E j z))
    (Cbox J : ℕ) (z : Lattice d) (h : ℕ) :
    MeasurableSet (crossFailUnion E Cbox J z h) := by
  refine MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_crossFailEvent hE Cbox J z l (crossCount J l)

/-- The levels above which no crossing fails. -/
def crossHeightSet (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (z : Lattice d)
    (ω : Ω) : Set ℕ := {h | ω ∉ crossFailUnion E Cbox J z h}

theorem crossHeightSet_upward {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ}
    {z : Lattice d} {ω : Ω} {h h' : ℕ} (hmem : h ∈ crossHeightSet E Cbox J z ω)
    (hle : h ≤ h') : h' ∈ crossHeightSet E Cbox J z ω :=
  fun hcon => hmem (crossFailUnion_antitone E Cbox J z hle hcon)

/-- The manuscript's `L_cross(z)`, as a least upward-closed threshold. -/
def crossMinScale (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (z : Lattice d)
    (ω : Ω) : ℕ := sInf (crossHeightSet E Cbox J z ω)

/-- The crossing minimal scale, kept above the deterministic base scale. -/
def crossScale (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (z : Lattice d)
    (ω : Ω) : ℕ := crossL0 Cbox J + crossMinScale E Cbox J z ω

theorem one_le_crossScale (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ)
    (z : Lattice d) (ω : Ω) : 1 ≤ crossScale E Cbox J z ω := by
  rw [crossScale]
  have := one_le_crossL0 Cbox J
  omega

/-- Above the crossing scale, no crossing fails. -/
theorem not_mem_crossFailEvent_of_crossScale_le {E : ℕ → Lattice d → Set Ω}
    {Cbox J : ℕ} {z : Lattice d} {ω : Ω}
    (hne : (crossHeightSet E Cbox J z ω).Nonempty) {l : ℕ}
    (hl : crossScale E Cbox J z ω ≤ l) :
    ω ∉ crossFailEvent E Cbox J z l (crossCount J l) := by
  intro hmem
  have hmin : crossMinScale E Cbox J z ω ∈ crossHeightSet E Cbox J z ω :=
    Nat.sInf_mem hne
  exact hmin (Set.mem_iUnion₂.mpr ⟨l, by rw [crossScale] at hl; omega, hmem⟩)

theorem measurable_crossMinScale [MeasurableSpace Ω] {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox J : ℕ) (z : Lattice d) :
    Measurable (crossMinScale E Cbox J z) := by
  classical
  refine measurable_to_countable' fun j => ?_
  show MeasurableSet {ω | crossMinScale E Cbox J z ω = j}
  rcases j with _ | j
  · have heq : {ω : Ω | crossMinScale E Cbox J z ω = 0} =
        (crossFailUnion E Cbox J z 0)ᶜ ∪ ⋂ h : ℕ, crossFailUnion E Cbox J z h := by
      ext ω
      simp only [crossMinScale, Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff,
        Set.mem_iInter]
      rw [Nat.sInf_eq_zero]
      constructor
      · rintro (h0 | hempty)
        · exact Or.inl h0
        · refine Or.inr fun h => ?_
          by_contra hcon
          exact (Set.eq_empty_iff_forall_notMem.mp hempty) h hcon
      · rintro (h0 | hall)
        · exact Or.inl h0
        · refine Or.inr (Set.eq_empty_iff_forall_notMem.mpr fun h hh => ?_)
          exact hh (hall h)
    rw [heq]
    exact (measurableSet_crossFailUnion hE Cbox J z 0).compl.union
      (MeasurableSet.iInter fun h => measurableSet_crossFailUnion hE Cbox J z h)
  · have heq : {ω : Ω | crossMinScale E Cbox J z ω = j + 1} =
        (crossFailUnion E Cbox J z (j + 1))ᶜ ∩ crossFailUnion E Cbox J z j := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · intro hval
        have hne : (crossHeightSet E Cbox J z ω).Nonempty := by
          by_contra hcon
          rw [Set.not_nonempty_iff_eq_empty] at hcon
          simp only [crossMinScale, hcon, Nat.sInf_empty] at hval
          omega
        have hmem : crossMinScale E Cbox J z ω ∈ crossHeightSet E Cbox J z ω :=
          Nat.sInf_mem hne
        rw [hval] at hmem
        refine ⟨hmem, ?_⟩
        by_contra hcon
        have hjmem : j ∈ crossHeightSet E Cbox J z ω := hcon
        have hsle := Nat.sInf_le hjmem
        have hval' : sInf (crossHeightSet E Cbox J z ω) = j + 1 := hval
        omega
      · rintro ⟨h1, h2⟩
        have hmem : j + 1 ∈ crossHeightSet E Cbox J z ω := h1
        have hle : crossMinScale E Cbox J z ω ≤ j + 1 := Nat.sInf_le hmem
        have hne : (crossHeightSet E Cbox J z ω).Nonempty := ⟨j + 1, hmem⟩
        by_contra hcon
        have hlt : crossMinScale E Cbox J z ω ≤ j := by omega
        exact (crossHeightSet_upward (Nat.sInf_mem hne) hlt) h2
    rw [heq]
    exact (measurableSet_crossFailUnion hE Cbox J z (j + 1)).compl.inter
      (measurableSet_crossFailUnion hE Cbox J z j)

/-- **The crossing scale is measurable.**  A constant shift of the measurable minimal
scale; the composition is the one already used inline inside `ogammaLE_crossScale`. -/
theorem measurable_crossScale [MeasurableSpace Ω] {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox J : ℕ) (z : Lattice d) :
    Measurable (crossScale E Cbox J z) :=
  (measurable_crossMinScale hE Cbox J z).const_add (crossL0 Cbox J)

/-! ## Monotonicity of the `O_{Γ₁}` bound in the observable -/

theorem ogammaLE_mono_le [MeasurableSpace Ω] {mu : Measure Ω} {A : ℝ} {X Y : Ω → ℝ}
    (hA : 0 < A) (hXmeas : Measurable X) (hXY : ∀ ω, X ω ≤ Y ω)
    (hY : SubdiffusiveProcess.OGammaLE mu 1 A Y) : SubdiffusiveProcess.OGammaLE mu 1 A X := by
  obtain ⟨hint, hbound⟩ := hY
  have hle : ∀ ω, Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ)) ≤
      Real.exp ((A⁻¹ * max (Y ω) 0) ^ (1 : ℝ)) := by
    intro ω
    rw [Real.rpow_one, Real.rpow_one, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (max_le_max (hXY ω) le_rfl) (inv_nonneg.mpr hA.le)
  have hmeas : AEStronglyMeasurable
      (fun ω => Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ))) mu := by
    refine Measurable.aestronglyMeasurable ?_
    refine Real.measurable_exp.comp ?_
    simp only [Real.rpow_one]
    exact (measurable_const.mul ((hXmeas.max measurable_const)))
  have hint2 : Integrable (fun ω => Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ))) mu := by
    refine hint.mono' hmeas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hle ω
  exact ⟨hint2, (integral_mono hint2 hint hle).trans hbound⟩

/-! ## The geometric tail of the crossing minimal scale -/

theorem measure_crossFailUnion_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep J : ℕ)
    {Cprob cprob q : ℝ} (hcprob : 0 < cprob) (hq0 : 0 ≤ q) (hCbox : 1 ≤ Cbox)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ crossBeta d cprob * q)
    (hth2 : Real.log (8 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ crossBeta d cprob * q)
    (hth3 : crossEntropy d Cbox Cdep J Cprob ≤
      crossBeta d cprob * q / (4 * crossAc Cbox Cdep J))
    (hlog2 : Real.log 2 ≤ crossRate d Cbox Cdep J cprob * q / 2)
    (z : Lattice d) (h : ℕ) :
    mu (crossFailUnion E Cbox J z h) ≤
      2 * ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep J cprob * q / 2))) ^
        (crossL0 Cbox J + h) := by
  classical
  set r : ℝ := crossRate d Cbox Cdep J cprob * q with hrdef
  set M : ℕ := crossL0 Cbox J + h with hM
  set theta : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(r / 2))) with htheta
  have hrpos : 0 ≤ r := by
    rw [hrdef]
    exact mul_nonneg (crossRate_pos hcprob hCbox).le hq0
  have hthetahalf : theta ≤ 2⁻¹ := by
    rw [htheta, show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (2⁻¹) by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show (2 : ℝ)⁻¹ = Real.exp (-(Real.log 2)) by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpow : ∀ n : ℕ, theta ^ n = ENNReal.ofReal (Real.exp (-(r / 2) * (n : ℝ))) := by
    intro n
    rw [htheta, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    ring
  have hstep : ∀ l : ℕ,
      mu (⋃ _ : M ≤ l, crossFailEvent E Cbox J z l (crossCount J l)) ≤
        ENNReal.ofReal (Real.exp (-(r / 2) * (M : ℝ))) * theta ^ l := by
    intro l
    by_cases hl : M ≤ l
    · have hl1 : 12 * Cbox ≤ l := by rw [hM, crossL0] at hl; omega
      have hl2 : 24 * J ≤ l := by rw [hM, crossL0] at hl; omega
      have hl3 : 1 ≤ l := by rw [hM, crossL0] at hl; omega
      have hbound := measure_crossFailEvent_le_exp mu E Cbox Cdep J hcprob hq0 hCbox
        hsc hr hprob hth1 hth2 hth3 z l hl1 hl2 hl3
      have huniv : (⋃ _ : M ≤ l, crossFailEvent E Cbox J z l (crossCount J l)) =
          crossFailEvent E Cbox J z l (crossCount J l) := by
        simp [hl]
      rw [huniv]
      refine hbound.trans ?_
      rw [hpow l, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have hMl : (M : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
      have hlR : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
      nlinarith [hrpos, hMl]
    · have hempty : (⋃ _ : M ≤ l, crossFailEvent E Cbox J z l (crossCount J l)) = ∅ := by
        simp [hl]
      rw [hempty]
      simp
  calc mu (crossFailUnion E Cbox J z h)
      ≤ ∑' l : ℕ, mu (⋃ _ : M ≤ l, crossFailEvent E Cbox J z l (crossCount J l)) :=
        measure_iUnion_le _
    _ ≤ ∑' l : ℕ, ENNReal.ofReal (Real.exp (-(r / 2) * (M : ℝ))) * theta ^ l :=
        ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal (Real.exp (-(r / 2) * (M : ℝ))) * (1 - theta)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ ≤ theta ^ M * 2 := by
        rw [hpow M]
        refine mul_le_mul' le_rfl ?_
        have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ 1 - theta := by
          refine ENNReal.le_sub_of_add_le_right
            (by rw [htheta]; exact ENNReal.ofReal_ne_top) ?_
          calc (2 : ℝ≥0∞)⁻¹ + theta ≤ 2⁻¹ + 2⁻¹ := add_le_add le_rfl hthetahalf
            _ = 1 := ENNReal.inv_two_add_inv_two
        calc (1 - theta)⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹)⁻¹ := ENNReal.inv_le_inv.mpr hhalf
          _ = 2 := by simp
    _ = 2 * theta ^ M := by ring

/-! ## The tail of the minimal scale, and its `O_{Γ₁}` bound -/

theorem measure_crossMinScale_ge_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep J : ℕ)
    {Cprob cprob q : ℝ} (hcprob : 0 < cprob) (hq0 : 0 ≤ q) (hCbox : 1 ≤ Cbox)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ crossBeta d cprob * q)
    (hth2 : Real.log (8 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ crossBeta d cprob * q)
    (hth3 : crossEntropy d Cbox Cdep J Cprob ≤
      crossBeta d cprob * q / (4 * crossAc Cbox Cdep J))
    (hlog2 : Real.log 2 ≤ crossRate d Cbox Cdep J cprob * q / 2)
    (z : Lattice d) (k : ℕ) :
    mu {ω | k ≤ crossMinScale E Cbox J z ω} ≤
      2 * ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep J cprob * q / 2))) ^ k := by
  set theta : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep J cprob * q / 2))) with htheta
  have hthetale : theta ≤ 1 := by
    rw [htheta, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ crossRate d Cbox Cdep J cprob * q :=
      mul_nonneg (crossRate_pos hcprob hCbox).le hq0
    linarith
  rcases k with _ | j
  · simp only [pow_zero, mul_one]
    exact le_trans (prob_le_one) (by norm_num)
  · have hsub : {ω | j + 1 ≤ crossMinScale E Cbox J z ω} ⊆
        crossFailUnion E Cbox J z j := by
      intro ω hω
      by_contra hcon
      have hjmem : j ∈ crossHeightSet E Cbox J z ω := hcon
      have hsle := Nat.sInf_le hjmem
      have hω' : j + 1 ≤ sInf (crossHeightSet E Cbox J z ω) := hω
      omega
    refine (measure_mono hsub).trans ?_
    refine (measure_crossFailUnion_le mu E Cbox Cdep J hcprob hq0 hCbox hsc hr hprob
      hth1 hth2 hth3 hlog2 z j).trans ?_
    refine mul_le_mul' le_rfl ?_
    refine pow_le_pow_of_le_one (bot_le) hthetale ?_
    have := one_le_crossL0 Cbox J
    omega

theorem measure_crossHeightSet_not_nonempty_eq_zero [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω)
    (Cbox Cdep J : ℕ) {Cprob cprob q : ℝ} (hcprob : 0 < cprob) (hqpos : 0 < q)
    (hCbox : 1 ≤ Cbox)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ crossBeta d cprob * q)
    (hth2 : Real.log (8 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ crossBeta d cprob * q)
    (hth3 : crossEntropy d Cbox Cdep J Cprob ≤
      crossBeta d cprob * q / (4 * crossAc Cbox Cdep J))
    (hlog2 : Real.log 2 ≤ crossRate d Cbox Cdep J cprob * q / 2)
    (z : Lattice d) :
    mu {ω | ¬ (crossHeightSet E Cbox J z ω).Nonempty} = 0 := by
  set r2 : ℝ := crossRate d Cbox Cdep J cprob * q / 2 with hr2
  have hr2pos : 0 < r2 := by
    rw [hr2]
    have := crossRate_pos (d := d) (Cbox := Cbox) (Cdep := Cdep) (J := J) hcprob hCbox
    positivity
  have hexplt : Real.exp (-r2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hset : {ω : Ω | ¬ (crossHeightSet E Cbox J z ω).Nonempty} =
      ⋂ h : ℕ, crossFailUnion E Cbox J z h := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.not_nonempty_iff_eq_empty, Set.mem_iInter]
    constructor
    · intro hempty h
      by_contra hcon
      exact (Set.eq_empty_iff_forall_notMem.mp hempty) h hcon
    · intro hall
      exact Set.eq_empty_iff_forall_notMem.mpr fun h hh => hh (hall h)
  rw [hset]
  refine measure_eq_zero_of_le_geometric mu _
    (Cf := 2 * Real.exp (-r2 * (crossL0 Cbox J : ℝ)) * (1 - Real.exp (-r2))) hr2pos
    fun h => ?_
  refine (measure_mono (Set.iInter_subset _ h)).trans ?_
  refine (measure_crossFailUnion_le mu E Cbox Cdep J hcprob hqpos.le hCbox hsc hr hprob
    hth1 hth2 hth3 hlog2 z h).trans ?_
  have hpow : (ENNReal.ofReal (Real.exp (-r2))) ^ (crossL0 Cbox J + h) =
      ENNReal.ofReal (Real.exp (-r2 * ((crossL0 Cbox J + h : ℕ) : ℝ))) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [hpow, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by rw [ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have hne : 1 - Real.exp (-r2) ≠ 0 := by
    have : 0 < 1 - Real.exp (-r2) := by linarith
    linarith
  field_simp
  rw [← Real.exp_add]
  push_cast
  congr 1
  ring

/-- **The printed tail `L_cross(z) ≤ L₀ + O_{Γ₁}(C/q)`.** -/
theorem ogammaLE_crossScale [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep J : ℕ)
    {Cprob cprob q : ℝ} (hcprob : 0 < cprob) (hqpos : 0 < q) (hCbox : 1 ≤ Cbox)
    (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ crossBeta d cprob * q)
    (hth2 : Real.log (8 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ crossBeta d cprob * q)
    (hth3 : crossEntropy d Cbox Cdep J Cprob ≤
      crossBeta d cprob * q / (4 * crossAc Cbox Cdep J))
    (hlog2 : Real.log 2 ≤ crossRate d Cbox Cdep J cprob * q / 2)
    (z : Lattice d) :
    SubdiffusiveProcess.OGammaLE mu 1 (8 / crossRate d Cbox Cdep J cprob / q)
      (fun ω => (crossScale E Cbox J z ω : ℝ) - ((crossL0 Cbox J + 2 : ℕ) : ℝ)) := by
  set r2 : ℝ := crossRate d Cbox Cdep J cprob * q / 2 with hr2
  have hr2pos : 0 < r2 := by
    rw [hr2]
    have := crossRate_pos (d := d) (Cbox := Cbox) (Cdep := Cdep) (J := J) hcprob hCbox
    positivity
  set theta : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-r2)) with htheta
  have hthetapos : 0 < theta := by
    rw [htheta, ENNReal.ofReal_pos]
    exact Real.exp_pos _
  have hthetalt : theta < 1 := by
    rw [htheta, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
      (Real.exp_lt_one_iff.mpr (by linarith))
  have htail : ∀ k : ℕ, 0 ≤ k →
      mu {ω | k ≤ crossMinScale E Cbox J z ω} ≤ 2 * theta ^ k := by
    intro k _
    rw [htheta, hr2]
    exact measure_crossMinScale_ge_le mu E Cbox Cdep J hcprob hqpos.le hCbox hsc hr
      hprob hth1 hth2 hth3 hlog2 z k
  have hbridge := Section8Resolvent.ogammaLE_of_geometric_tail (mu := mu)
    (measurable_crossMinScale hE Cbox J z) (C := 2) (theta := theta)
    (by simp) hthetapos hthetalt 0 htail
  rw [htheta, stoppingTailRate_ofReal_exp_neg] at hbridge
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hres := ogammaLE_one_rescale (mu := mu) hlog3 hbridge
  -- the centre is at most `2`
  set br : ℕ := Section8Resolvent.stoppingTailCenterBracket 2 theta 0 with hbr
  have hbrle : br ≤ 1 := by
    rw [hbr, Section8Resolvent.stoppingTailCenterBracket, htheta,
      stoppingTailRate_ofReal_exp_neg]
    have h2 : (max 1 ((2 : ℝ≥0∞)).toReal) = 2 := by
      rw [ENNReal.toReal_ofNat]
      norm_num
    rw [h2]
    have hceil : ⌈Real.log 2 / r2⌉₊ ≤ 1 := by
      refine Nat.ceil_le.mpr ?_
      rw [Nat.cast_one, div_le_one hr2pos]
      exact hlog2
    omega
  have hcentre : Section8Resolvent.stoppingTailCenter 2 theta 0 / Real.log 3 =
      ((br + 1 : ℕ) : ℝ) := by
    rw [Section8Resolvent.stoppingTailCenter, ← hbr]
    field_simp
  rw [hcentre] at hres
  have hamp : Section8Resolvent.stoppingTailGammaOneConstant * Real.log 3 / r2 /
      Real.log 3 = 8 / crossRate d Cbox Cdep J cprob / q := by
    rw [Section8Resolvent.stoppingTailGammaOneConstant, hr2]
    have hcr : crossRate d Cbox Cdep J cprob ≠ 0 :=
      ne_of_gt (crossRate_pos hcprob hCbox)
    field_simp
    ring
  rw [hamp] at hres
  refine ogammaLE_mono_le
    (div_pos (div_pos (by norm_num) (crossRate_pos hcprob hCbox)) hqpos) ?_ ?_ hres
  · refine Measurable.sub ?_ measurable_const
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((measurable_crossMinScale hE Cbox J z).const_add (crossL0 Cbox J))
  · intro ω
    have hbr2 : br + 1 ≤ 2 := by omega
    have hbrR : ((br : ℝ) + 1) ≤ 2 := by exact_mod_cast hbr2
    show ((crossL0 Cbox J + crossMinScale E Cbox J z ω : ℕ) : ℝ) -
      ((crossL0 Cbox J + 2 : ℕ) : ℝ) ≤
      ((crossMinScale E Cbox J z ω : ℕ) : ℝ) - ((br + 1 : ℕ) : ℝ)
    push_cast
    linarith

/-! ## Clause (i) for the concrete field -/

/-- The density constant printed by the crossing clause. -/
def crossDensity (d Cbox J : ℕ) : ℝ :=
  1 / (2 * ((12 * J + 12 : ℕ) : ℝ) * (((2 * (2 * Cbox) + 1) ^ d : ℕ) : ℝ))

theorem crossDensity_pos (d Cbox J : ℕ) : 0 < crossDensity d Cbox J := by
  rw [crossDensity]
  have h1 : (0 : ℝ) < ((12 * J + 12 : ℕ) : ℝ) := by
    have : 0 < 12 * J + 12 := by omega
    exact_mod_cast this
  have h2 : (0 : ℝ) < (((2 * (2 * Cbox) + 1) ^ d : ℕ) : ℝ) := by
    have : 0 < (2 * (2 * Cbox) + 1) ^ d := by positivity
    exact_mod_cast this
  positivity

theorem crossDensity_mul_le (d Cbox J l : ℕ) (hl : 24 * J + 24 ≤ l) :
    crossDensity d Cbox J * (l : ℝ) * (((2 * (2 * Cbox) + 1) ^ d : ℕ) : ℝ) ≤
      ((crossCount J l : ℕ) : ℝ) := by
  set D : ℝ := (((2 * (2 * Cbox) + 1) ^ d : ℕ) : ℝ) with hD
  set b : ℝ := ((12 * J + 12 : ℕ) : ℝ) with hb
  have hDpos : 0 < D := by
    rw [hD]
    have : 0 < (2 * (2 * Cbox) + 1) ^ d := by positivity
    exact_mod_cast this
  have hbpos : 0 < b := by
    rw [hb]
    have : 0 < 12 * J + 12 := by omega
    exact_mod_cast this
  have hlt : l < (crossCount J l + 1) * (12 * J + 12) := by
    have hb : 0 < 12 * J + 12 := by omega
    have h1 : (12 * J + 12) * (l / (12 * J + 12)) + l % (12 * J + 12) = l :=
      Nat.div_add_mod l (12 * J + 12)
    have h2 : l % (12 * J + 12) < 12 * J + 12 := Nat.mod_lt l hb
    rw [crossCount]
    calc l = (12 * J + 12) * (l / (12 * J + 12)) + l % (12 * J + 12) := h1.symm
      _ < (12 * J + 12) * (l / (12 * J + 12)) + (12 * J + 12) := by omega
      _ = (l / (12 * J + 12) + 1) * (12 * J + 12) := by ring
  have hltR : (l : ℝ) < (((crossCount J l : ℕ) : ℝ) + 1) * b := by
    have := (Nat.cast_lt (α := ℝ)).mpr hlt
    rw [hb]
    push_cast at this ⊢
    linarith
  have hlb : 2 * b ≤ (l : ℝ) := by
    have hnat : 2 * (12 * J + 12) ≤ l := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    rw [hb]
    push_cast at this ⊢
    linarith
  have hkey : (l : ℝ) / (2 * b) ≤ ((crossCount J l : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hltR, hlb]
  refine le_trans (le_of_eq ?_) hkey
  rw [crossDensity, ← hD, ← hb]
  field_simp

/-- **`[ASD, Lemma B.1(2)]` for the concrete field.**  Clause (i) of the
multiscale percolation geometry holds almost surely with the witness
`crossScale`, which is at least `1` and has the printed `O_{Γ₁}(C/q)` tail. -/
theorem exists_asd_clause_one (d Cbox Cdep J : ℕ) (Cprob cprob : ℝ)
    (hCbox : 1 ≤ Cbox) (hcprob : 0 < cprob) :
    ∃ q0 L0 : ℕ, ∃ ccross Ccross : ℝ, 0 < ccross ∧ 0 < Ccross ∧ 1 ≤ L0 ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (Ccross / q)
            (fun omega => (crossing z omega : ℝ) - L0)) ∧
          (∀ᵐ omega ∂mu, ∀ (z : Lattice d) (l : ℕ), crossing z omega ≤ l →
            ∀ path : List (Lattice d), IsJStepListPath J path →
            (∃ v ∈ path, InLatticeBallReal z v (l / 3 : ℝ)) →
            (∃ v ∈ path, ¬ InLatticeBallReal z v (2 * l / 3 : ℝ)) →
            ∃ chosen : List (Lattice d),
              chosen.Sublist path ∧ ccross * l ≤ chosen.length ∧
                (∀ v ∈ chosen,
                  IsPercolationGoodSite E Cbox omega v ∧
                    latticeBallSet v Cbox ⊆
                      latticeBallSet z (3 * l / 4 : ℝ) \
                        latticeBallSet z (l / 4 : ℝ)) ∧
                chosen.Pairwise fun v w ↦
                  Disjoint (latticeBallSet v Cbox) (latticeBallSet w Cbox)) ∧
          (∀ z, Measurable (crossing z)) := by
  classical
  set beta : ℝ := crossBeta d cprob with hbeta
  set rate : ℝ := crossRate d Cbox Cdep J cprob with hrate
  have hbetapos : 0 < beta := crossBeta_pos hcprob
  have hratepos : 0 < rate := crossRate_pos hcprob hCbox
  set V1 : ℝ := (3 * (d : ℝ) * Real.log 3 + 1) / beta with hV1
  set V2 : ℝ := Real.log (8 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) *
    crossScaleConst d Cbox Cdep Cprob) / beta with hV2
  set V3 : ℝ := 4 * crossAc Cbox Cdep J * crossEntropy d Cbox Cdep J Cprob / beta
    with hV3
  set V4 : ℝ := 2 * Real.log 2 / rate with hV4
  set Q : ℝ := max (max V1 V2) (max (max V3 V4) 1) with hQ
  refine ⟨⌈Q⌉₊, crossL0 Cbox J + 2, crossDensity d Cbox J, 8 / rate,
    crossDensity_pos d Cbox J, by positivity, by
      have := one_le_crossL0 Cbox J; omega, ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw
  have hQq : Q ≤ q := le_trans (Nat.le_ceil Q) hq
  have hqpos : 0 < q := by
    have h1 : (1 : ℝ) ≤ Q := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ beta * q := by
    have : V1 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQq
    rw [hV1, div_le_iff₀ hbetapos] at this
    linarith
  have hth2 : Real.log (8 * ((2 ^ d * (J + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ beta * q := by
    have : V2 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQq
    rw [hV2, div_le_iff₀ hbetapos] at this
    linarith
  have hth3 : crossEntropy d Cbox Cdep J Cprob ≤
      beta * q / (4 * crossAc Cbox Cdep J) := by
    have hac : 0 < crossAc Cbox Cdep J := crossAc_pos hCbox
    have : V3 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) hQq)
    rw [hV3, div_le_iff₀ hbetapos] at this
    rw [le_div_iff₀ (by linarith)]
    nlinarith [this]
  have hlog2 : Real.log 2 ≤ rate * q / 2 := by
    have : V4 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) hQq)
    rw [hV4, div_le_iff₀ hratepos] at this
    linarith
  have hE : ∀ j z, MeasurableSet (E j z) := hlaw.1
  refine ⟨fun z ω => crossScale E Cbox J z ω, fun z ω => one_le_crossScale E Cbox J z ω,
    ?_, ?_, ?_⟩
  · intro z
    have h := ogammaLE_crossScale mu E Cbox Cdep J hcprob hqpos hCbox hE hsc hr hprob
      (by rw [hbeta] at hth1; exact hth1) (by rw [hbeta] at hth2; exact hth2)
      (by rw [hbeta] at hth3; exact hth3) (by rw [hrate] at hlog2; exact hlog2) z
    rw [hrate]
    exact h
  · have hae : ∀ᵐ ω ∂mu, ∀ z : Lattice d, (crossHeightSet E Cbox J z ω).Nonempty := by
      refine ae_all_iff.2 fun z => ?_
      rw [ae_iff]
      exact measure_crossHeightSet_not_nonempty_eq_zero mu E Cbox Cdep J hcprob hqpos
        hCbox hsc hr hprob (by rw [hbeta] at hth1; exact hth1)
        (by rw [hbeta] at hth2; exact hth2) (by rw [hbeta] at hth3; exact hth3)
        (by rw [hrate] at hlog2; exact hlog2) z
    filter_upwards [hae] with ω hω
    intro z l hl
    have hne := hω z
    have hnotfail := not_mem_crossFailEvent_of_crossScale_le hne hl
    have hgc : CrossingGoodCount E Cbox J ω z l (crossCount J l) := by
      by_contra hcon
      exact hnotfail hcon
    have hlarge : 24 * J + 24 ≤ l := by
      have h1 : crossL0 Cbox J ≤ crossScale E Cbox J z ω := by
        rw [crossScale]; omega
      have := le_trans h1 hl
      rw [crossL0] at this
      omega
    exact crossingClause_of_crossingGoodCount
      (crossDensity_mul_le d Cbox J l hlarge) hgc
  · exact fun z => measurable_crossScale hE Cbox J z

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
