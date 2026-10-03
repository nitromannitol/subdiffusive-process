module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalZeroOne
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Constructions.Cylinders

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory MeasurableSpace Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## Measure plumbing -/

theorem measure_le_add_of_subset_union {X : Type*} [MeasurableSpace X] (mu : Measure X)
    {s t u : Set X} (h : s ⊆ t ∪ u) : mu s ≤ mu t + mu u :=
  (measure_mono h).trans (measure_union_le t u)

theorem measure_inter_le_inter_add_sdiff {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (A B C : Set X) : mu (A ∩ C) ≤ mu (B ∩ C) + mu (A \ B) := by
  refine measure_le_add_of_subset_union mu ?_
  intro x hx
  by_cases hb : x ∈ B
  · exact Or.inl ⟨hb, hx.2⟩
  · exact Or.inr ⟨hx.1, hb⟩

theorem measure_sdiff_add_sdiff_eq_symmDiff {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    mu (A \ B) + mu (B \ A) = mu (symmDiff A B) := by
  have hunion : symmDiff A B = (A \ B) ∪ (B \ A) := rfl
  rw [hunion, measure_union disjoint_sdiff_sdiff (hB.diff hA)]

theorem abs_toReal_sub_le_of_le_add {x y p q : ℝ≥0∞} {delta : ℝ} (hx : x ≠ ⊤) (hy : y ≠ ⊤)
    (hdelta : 0 ≤ delta) (h1 : x ≤ y + p) (h2 : y ≤ x + q)
    (hpq : p + q ≤ ENNReal.ofReal delta) : |x.toReal - y.toReal| ≤ delta := by
  have hpqtop : p + q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpq
  obtain ⟨hp, hq⟩ := ENNReal.add_ne_top.mp hpqtop
  have h1' : x.toReal ≤ y.toReal + p.toReal := by
    have h := ENNReal.toReal_mono (by finiteness) h1
    rwa [ENNReal.toReal_add hy hp] at h
  have h2' : y.toReal ≤ x.toReal + q.toReal := by
    have h := ENNReal.toReal_mono (by finiteness) h2
    rwa [ENNReal.toReal_add hx hq] at h
  have hpq' : p.toReal + q.toReal ≤ delta := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpq
    rwa [ENNReal.toReal_add hp hq, ENNReal.toReal_ofReal hdelta] at h
  have hp0 : (0 : ℝ) ≤ p.toReal := ENNReal.toReal_nonneg
  have hq0 : (0 : ℝ) ≤ q.toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- Two events close in symmetric difference have close intersections with any third event. -/
theorem abs_toReal_measure_inter_sub_le {X : Type*} [MeasurableSpace X] (nu : Measure X)
    [IsFiniteMeasure nu] {A B C : Set X} {delta : ℝ} (hdelta : 0 ≤ delta)
    (h : nu (A \ B) + nu (B \ A) ≤ ENNReal.ofReal delta) :
    |(nu (A ∩ C)).toReal - (nu (B ∩ C)).toReal| ≤ delta :=
  abs_toReal_sub_le_of_le_add (measure_ne_top _ _) (measure_ne_top _ _) hdelta
    (measure_inter_le_inter_add_sdiff nu A B C)
    (measure_inter_le_inter_add_sdiff nu B A C) h

/-! ## The algebra of finitely based configuration events -/

/-- The events of the configuration space that depend on finitely many `(scale, site)` pairs. -/
def FinitelyBasedConfig (d : ℕ) : Set (Set (ℕ × Lattice d → ℝ)) :=
  {A | ∃ F : Finset (ℕ × Lattice d),
    MeasurableSet[cylinderEvents (X := fun _ : ℕ × Lattice d => ℝ)
      (F : Set (ℕ × Lattice d))] A}

theorem isSetAlgebra_finitelyBasedConfig : IsSetAlgebra (FinitelyBasedConfig d) := by
  refine ⟨⟨∅, @MeasurableSet.empty _ (cylinderEvents (X := fun _ : ℕ × Lattice d => ℝ)
    ((∅ : Finset (ℕ × Lattice d)) : Set (ℕ × Lattice d)))⟩, ?_, ?_⟩
  · rintro s ⟨F, hF⟩
    exact ⟨F, hF.compl⟩
  · rintro s t ⟨F, hF⟩ ⟨G, hG⟩
    refine ⟨F ∪ G, ?_⟩
    have h1 := cylinderEvents_mono (X := fun _ : ℕ × Lattice d => ℝ)
      (Δ₁ := (F : Set (ℕ × Lattice d))) (Δ₂ := ((F ∪ G : Finset (ℕ × Lattice d)) : Set (ℕ × Lattice d)))
      (by intro x hx; simp only [Finset.coe_union]; exact Or.inl hx) _ hF
    have h2 := cylinderEvents_mono (X := fun _ : ℕ × Lattice d => ℝ)
      (Δ₁ := (G : Set (ℕ × Lattice d))) (Δ₂ := ((F ∪ G : Finset (ℕ × Lattice d)) : Set (ℕ × Lattice d)))
      (by intro x hx; simp only [Finset.coe_union]; exact Or.inr hx) _ hG
    exact h1.union h2

theorem generateFrom_finitelyBasedConfig :
    generateFrom (FinitelyBasedConfig d) =
      (MeasurableSpace.pi : MeasurableSpace (ℕ × Lattice d → ℝ)) := by
  refine le_antisymm (generateFrom_le ?_) ?_
  · rintro A ⟨F, hF⟩
    exact cylinderEvents_le_pi _ hF
  · rw [← cylinderEvents_univ (X := fun _ : ℕ × Lattice d => ℝ)]
    refine iSup₂_le fun i _ => ?_
    intro A hA
    refine measurableSet_generateFrom ⟨{i}, ?_⟩
    have h : cylinderEvents (X := fun _ : ℕ × Lattice d => ℝ)
        (({i} : Finset (ℕ × Lattice d)) : Set (ℕ × Lattice d)) =
        MeasurableSpace.comap (fun σ : ℕ × Lattice d → ℝ => σ i) inferInstance := by
      simp [cylinderEvents]
    exact h ▸ hA

/-- **The cylinder approximation.**  Every measurable configuration event is approximated, in
symmetric difference, by an event depending on finitely many `(scale, site)` pairs. -/
theorem exists_finitelyBasedConfig_measure_sdiff_le (nu : Measure (ℕ × Lattice d → ℝ))
    [IsFiniteMeasure nu] {A : Set (ℕ × Lattice d → ℝ)} (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Set (ℕ × Lattice d → ℝ), MeasurableSet B ∧ B ∈ FinitelyBasedConfig d ∧
      nu (A \ B) + nu (B \ A) ≤ ENNReal.ofReal ε := by
  have hdense : nu.MeasureDense (FinitelyBasedConfig d) :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite nu isSetAlgebra_finitelyBasedConfig
      generateFrom_finitelyBasedConfig.symm
  obtain ⟨B, hB, hlt⟩ := hdense.approx A hA (measure_ne_top _ _) ε hε
  refine ⟨B, hdense.measurable B hB, hB, ?_⟩
  rw [measure_sdiff_add_sdiff_eq_symmDiff nu hA (hdense.measurable B hB)]
  exact hlt.le

/-! ## The 0–1 law from asymptotic, rather than exact, independence -/

/-- **Asymptotic self-independence.**  `A` is approximated in measure, to arbitrary accuracy,
by events *approximately* independent of it.  This is the weakening of
`ApproximableByIndependent` that the cylinder route can actually supply: a shift-invariant
event is only asymptotically independent of its far translates, never exactly. -/
def ApproxIndepSelf [MeasurableSpace Ω] (mu : Measure Ω) (A : Set Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : Set Ω,
    mu (A \ B) + mu (B \ A) ≤ ENNReal.ofReal ε ∧
      |(mu (A ∩ B)).toReal - (mu A).toReal * (mu B).toReal| ≤ ε

theorem approxIndepSelf_of_approximableByIndependent [MeasurableSpace Ω] {mu : Measure Ω}
    {A : Set Ω} (h : ApproximableByIndependent mu A) : ApproxIndepSelf mu A := by
  intro ε hε
  obtain ⟨B, hsym, hindep⟩ := h ε hε
  refine ⟨B, hsym, ?_⟩
  rw [hindep, ENNReal.toReal_mul]
  simpa using hε.le

/-- **The 0–1 law, asymptotic form.**  An event asymptotically independent of itself has
probability `0` or `1`. -/
theorem measure_eq_zero_or_one_of_approxIndepSelf [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {A : Set Ω} (h : ApproxIndepSelf mu A) :
    mu A = 0 ∨ mu A = 1 := by
  have h0 : (0 : ℝ) ≤ (mu A).toReal := ENNReal.toReal_nonneg
  have hle : (mu A).toReal ≤ 1 := by
    have := prob_le_one (μ := mu) (s := A)
    simpa using ENNReal.toReal_mono (by simp) this
  have key : (mu A).toReal = (mu A).toReal * (mu A).toReal := by
    refine eq_sq_of_forall_pos_abs_sub_le fun ε hε => ?_
    obtain ⟨B, hsym, hindep⟩ := h (ε / 2) (by linarith)
    have hne : ENNReal.ofReal (ε / 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    obtain ⟨h1, h2⟩ := abs_toReal_sub_toReal_inter_le mu A B hne hsym
    rw [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ε / 2)] at h1 h2
    have ha := abs_le.mp h1
    have hb := abs_le.mp h2
    have hc := abs_le.mp hindep
    have hdiff : |(mu B).toReal - (mu A).toReal| ≤ ε := by
      rw [abs_le]; constructor <;> linarith
    have hd := abs_le.mp hdiff
    have hupper : (mu A).toReal * ((mu B).toReal - (mu A).toReal) ≤ ε := by nlinarith
    have hlower : -ε ≤ (mu A).toReal * ((mu B).toReal - (mu A).toReal) := by nlinarith
    have hexp : (mu A).toReal * (mu B).toReal - (mu A).toReal * (mu A).toReal =
        (mu A).toReal * ((mu B).toReal - (mu A).toReal) := by ring
    rw [abs_le]
    constructor <;> linarith
  rcases eq_zero_or_one_of_eq_sq key with hz | ho
  · exact Or.inl (((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top mu A))
  · exact Or.inr ((ENNReal.toReal_eq_one_iff (mu A)).mp ho)

/-- **`[DRS]` condition P1 from asymptotic self-independence.** -/
theorem drsConditionP1_of_approxIndepSelf [MeasurableSpace Ω] {mu : Measure Ω}
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω}
    (hlaw : TranslationInvariantEventLaw mu E)
    (happrox : ∀ A : Set (ℕ × Lattice d → ℝ), MeasurableSet A →
      (∀ a : Lattice d, configShift a ⁻¹' A = A) →
      ApproxIndepSelf (Measure.map (eventFieldConfiguration E) mu) A) :
    DRSConditionP1 mu E := by
  haveI : IsProbabilityMeasure (Measure.map (eventFieldConfiguration E) mu) :=
    isProbabilityMeasure_map_eventFieldConfiguration hlaw
  exact ⟨hlaw, fun A hA hinv =>
    measure_eq_zero_or_one_of_approxIndepSelf _ (happrox A hA hinv)⟩

/-! ## The configuration law is shift invariant -/

theorem measurable_configShift (a : Lattice d) : Measurable (configShift (d := d) a) := by
  refine measurable_pi_iff.mpr fun p => ?_
  exact measurable_pi_apply (p.1, p.2 + a)

theorem map_configShift_map_eventFieldConfiguration [MeasurableSpace Ω] {mu : Measure Ω}
    {E : ℕ → Lattice d → Set Ω} (hlaw : TranslationInvariantEventLaw mu E) (a : Lattice d) :
    Measure.map (configShift a) (Measure.map (eventFieldConfiguration E) mu) =
      Measure.map (eventFieldConfiguration E) mu := by
  rw [Measure.map_map (measurable_configShift a)
    (measurable_eventFieldConfiguration hlaw.1)]
  have hcomp : configShift a ∘ eventFieldConfiguration E =
      translateEventFieldConfiguration E a := rfl
  rw [hcomp]
  exact hlaw.2 a

theorem measure_preimage_configShift {nu : Measure (ℕ × Lattice d → ℝ)} {a : Lattice d}
    (hinv : Measure.map (configShift a) nu = nu) {X : Set (ℕ × Lattice d → ℝ)}
    (hX : MeasurableSet X) : nu (configShift a ⁻¹' X) = nu X := by
  conv_rhs => rw [← hinv]
  rw [Measure.map_apply (measurable_configShift a) hX]

theorem toReal_measure_le_one {X : Type*} [MeasurableSpace X] (nu : Measure X)
    [IsProbabilityMeasure nu] (S : Set X) : (nu S).toReal ≤ 1 := by
  have := prob_le_one (μ := nu) (s := S)
  simpa using ENNReal.toReal_mono (by simp) this

/-! ## The residual and the assembly -/



def CylinderShiftIndependence [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) : Prop :=
  ∀ (F : Finset (ℕ × Lattice d)) (B : Set (ℕ × Lattice d → ℝ)),
    MeasurableSet[cylinderEvents (X := fun _ : ℕ × Lattice d => ℝ)
      (F : Set (ℕ × Lattice d))] B →
    ∃ a : Lattice d,
      Measure.map (eventFieldConfiguration E) mu (B ∩ configShift a ⁻¹' B) =
        Measure.map (eventFieldConfiguration E) mu B *
          Measure.map (eventFieldConfiguration E) mu (configShift a ⁻¹' B)

/-- **The assembly.**  Cylinder approximation plus the residual gives asymptotic
self-independence of every shift-invariant event. -/
theorem approxIndepSelf_of_cylinderShiftIndependence [MeasurableSpace Ω] {mu : Measure Ω}
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω}
    (hlaw : TranslationInvariantEventLaw mu E) (hind : CylinderShiftIndependence mu E)
    {A : Set (ℕ × Lattice d → ℝ)} (hA : MeasurableSet A)
    (hinv : ∀ a : Lattice d, configShift a ⁻¹' A = A) :
    ApproxIndepSelf (Measure.map (eventFieldConfiguration E) mu) A := by
  haveI : IsProbabilityMeasure (Measure.map (eventFieldConfiguration E) mu) :=
    isProbabilityMeasure_map_eventFieldConfiguration hlaw
  intro ε hε
  obtain ⟨B0, hB0, ⟨F, hF⟩, hsym⟩ :=
    exists_finitelyBasedConfig_measure_sdiff_le (Measure.map (eventFieldConfiguration E) mu)
      hA (half_pos hε)
  obtain ⟨a, hindep⟩ := hind F B0 hF
  have hshift := map_configShift_map_eventFieldConfiguration hlaw a
  have hC : MeasurableSet (configShift a ⁻¹' B0) := (measurable_configShift a) hB0
  refine ⟨configShift a ⁻¹' B0, ?_, ?_⟩
  · have e1 : A \ configShift a ⁻¹' B0 = configShift a ⁻¹' (A \ B0) := by
      rw [Set.preimage_diff, hinv a]
    have e2 : configShift a ⁻¹' B0 \ A = configShift a ⁻¹' (B0 \ A) := by
      rw [Set.preimage_diff, hinv a]
    rw [e1, e2, measure_preimage_configShift hshift (hA.diff hB0),
      measure_preimage_configShift hshift (hB0.diff hA)]
    exact hsym.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · have t1 : |(Measure.map (eventFieldConfiguration E) mu (A ∩ configShift a ⁻¹' B0)).toReal -
        (Measure.map (eventFieldConfiguration E) mu (B0 ∩ configShift a ⁻¹' B0)).toReal| ≤ ε / 2 :=
      abs_toReal_measure_inter_sub_le _ (by linarith) hsym
    have t2 : (Measure.map (eventFieldConfiguration E) mu (B0 ∩ configShift a ⁻¹' B0)).toReal =
        (Measure.map (eventFieldConfiguration E) mu B0).toReal *
          (Measure.map (eventFieldConfiguration E) mu (configShift a ⁻¹' B0)).toReal := by
      rw [hindep, ENNReal.toReal_mul]
    have t3 : |(Measure.map (eventFieldConfiguration E) mu A).toReal -
        (Measure.map (eventFieldConfiguration E) mu B0).toReal| ≤ ε / 2 := by
      have h := abs_toReal_measure_inter_sub_le
        (Measure.map (eventFieldConfiguration E) mu) (C := Set.univ) (by linarith) hsym
      simpa using h
    have hc0 : (0 : ℝ) ≤
        (Measure.map (eventFieldConfiguration E) mu (configShift a ⁻¹' B0)).toReal :=
      ENNReal.toReal_nonneg
    have hc1 : (Measure.map (eventFieldConfiguration E) mu (configShift a ⁻¹' B0)).toReal ≤ 1 :=
      toReal_measure_le_one _ _
    have hd := abs_le.mp t1
    have he := abs_le.mp t3
    have hexp : (Measure.map (eventFieldConfiguration E) mu B0).toReal *
          (Measure.map (eventFieldConfiguration E) mu (configShift a ⁻¹' B0)).toReal -
        (Measure.map (eventFieldConfiguration E) mu A).toReal *
          (Measure.map (eventFieldConfiguration E) mu (configShift a ⁻¹' B0)).toReal =
        ((Measure.map (eventFieldConfiguration E) mu B0).toReal -
          (Measure.map (eventFieldConfiguration E) mu A).toReal) *
          (Measure.map (eventFieldConfiguration E) mu (configShift a ⁻¹' B0)).toReal := by
      ring
    have hb1 : ((Measure.map (eventFieldConfiguration E) mu B0).toReal -
        (Measure.map (eventFieldConfiguration E) mu A).toReal) *
        (Measure.map (eventFieldConfiguration E) mu (configShift a ⁻¹' B0)).toReal ≤ ε / 2 := by
      nlinarith
    have hb2 : -(ε / 2) ≤ ((Measure.map (eventFieldConfiguration E) mu B0).toReal -
        (Measure.map (eventFieldConfiguration E) mu A).toReal) *
        (Measure.map (eventFieldConfiguration E) mu (configShift a ⁻¹' B0)).toReal := by
      nlinarith
    rw [abs_le]
    constructor <;> linarith

/-- **`[DRS]` condition P1, reduced to the residual.** -/
theorem drsConditionP1_of_cylinderShiftIndependence [MeasurableSpace Ω] {mu : Measure Ω}
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω}
    (hlaw : TranslationInvariantEventLaw mu E) (hind : CylinderShiftIndependence mu E) :
    DRSConditionP1 mu E :=
  drsConditionP1_of_approxIndepSelf hlaw fun _ hA hinvA =>
    approxIndepSelf_of_cylinderShiftIndependence hlaw hind hA hinvA

/-! ## Reducing the residual to an independence statement about the event field itself -/

/-- The σ-algebra generated by the events of a finite set of `(scale, site)` pairs. -/
def finiteFieldSigma (E : ℕ → Lattice d → Set Ω) (F : Finset (ℕ × Lattice d)) :
    MeasurableSpace Ω :=
  ⨆ p ∈ (F : Set (ℕ × Lattice d)), eventFieldSigma (E p.1) ({p.2} : Set (Lattice d))

/-- The indicator of a single event generates no more than that event. -/
theorem comap_indicator_le_eventFieldSigma [MeasurableSpace Ω]
    {E : Lattice d → Set Ω} {z : Lattice d} :
    MeasurableSpace.comap (fun ω => (E z).indicator (fun _ => (1 : ℝ)) ω) inferInstance ≤
      eventFieldSigma E ({z} : Set (Lattice d)) := by
  rintro _ ⟨S, -, rfl⟩
  have hz : MeasurableSet[eventFieldSigma E ({z} : Set (Lattice d))] (E z) :=
    measurableSet_event_of_mem rfl
  by_cases h1 : (1 : ℝ) ∈ S <;> by_cases h0 : (0 : ℝ) ∈ S
  · have hs : (fun ω => (E z).indicator (fun _ => (1 : ℝ)) ω) ⁻¹' S = Set.univ := by
      ext ω; by_cases hw : ω ∈ E z <;> simp [hw, h0, h1]
    rw [hs]
    exact @MeasurableSet.univ _ (eventFieldSigma E _)
  · have hs : (fun ω => (E z).indicator (fun _ => (1 : ℝ)) ω) ⁻¹' S = E z := by
      ext ω; by_cases hw : ω ∈ E z <;> simp [hw, h0, h1]
    rw [hs]
    exact hz
  · have hs : (fun ω => (E z).indicator (fun _ => (1 : ℝ)) ω) ⁻¹' S = (E z)ᶜ := by
      ext ω; by_cases hw : ω ∈ E z <;> simp [hw, h0, h1]
    rw [hs]
    exact hz.compl
  · have hs : (fun ω => (E z).indicator (fun _ => (1 : ℝ)) ω) ⁻¹' S = ∅ := by
      ext ω; by_cases hw : ω ∈ E z <;> simp [hw, h0, h1]
    rw [hs]
    exact @MeasurableSet.empty _ (eventFieldSigma E _)

/-- A finitely based configuration event pulls back into the finite-site field σ-algebra. -/
theorem comap_cylinderEvents_le [MeasurableSpace Ω] (E : ℕ → Lattice d → Set Ω)
    (F : Finset (ℕ × Lattice d)) :
    MeasurableSpace.comap (eventFieldConfiguration E)
        (cylinderEvents (X := fun _ : ℕ × Lattice d => ℝ) (F : Set (ℕ × Lattice d))) ≤
      finiteFieldSigma E F := by
  simp only [cylinderEvents, finiteFieldSigma, MeasurableSpace.comap_iSup]
  refine iSup₂_mono fun p _ => ?_
  rw [MeasurableSpace.comap_comp]
  exact comap_indicator_le_eventFieldSigma

/-- **The residual, restated on the event field.**  Every finite set of `(scale, site)` pairs
admits a translate whose field σ-algebra is independent of the original one. -/
def ShiftedFiniteFieldIndependence [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) : Prop :=
  ∀ F : Finset (ℕ × Lattice d), ∃ a : Lattice d,
    ProbabilityTheory.Indep (finiteFieldSigma E F)
      (finiteFieldSigma (fun j z => E j (z + a)) F) mu

/-- The configuration-space residual follows from the field-level one. -/
theorem cylinderShiftIndependence_of_shiftedFiniteFieldIndependence [MeasurableSpace Ω]
    {mu : Measure Ω} {E : ℕ → Lattice d → Set Ω} (hE : ∀ j z, MeasurableSet (E j z))
    (h : ShiftedFiniteFieldIndependence mu E) : CylinderShiftIndependence mu E := by
  intro F B hB
  obtain ⟨a, hindep⟩ := h F
  refine ⟨a, ?_⟩
  have hBpi : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hmeasf : Measurable (eventFieldConfiguration E) := measurable_eventFieldConfiguration hE
  have hCpi : MeasurableSet (configShift a ⁻¹' B) := (measurable_configShift a) hBpi
  have hX : MeasurableSet[finiteFieldSigma E F] (eventFieldConfiguration E ⁻¹' B) :=
    comap_cylinderEvents_le E F _ ⟨B, hB, rfl⟩
  have hY : MeasurableSet[finiteFieldSigma (fun j z => E j (z + a)) F]
      (eventFieldConfiguration E ⁻¹' (configShift a ⁻¹' B)) := by
    have hpre : eventFieldConfiguration E ⁻¹' (configShift a ⁻¹' B)
        = eventFieldConfiguration (fun j z => E j (z + a)) ⁻¹' B := rfl
    rw [hpre]
    exact comap_cylinderEvents_le (fun j z => E j (z + a)) F _ ⟨B, hB, rfl⟩
  rw [Measure.map_apply hmeasf (hBpi.inter hCpi), Measure.map_apply hmeasf hBpi,
    Measure.map_apply hmeasf hCpi, Set.preimage_inter]
  exact (ProbabilityTheory.Indep_iff _ _ mu).mp hindep _ _ hX hY

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
