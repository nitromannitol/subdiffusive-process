module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTruncation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-- A finite intersection of events of one scale is measurable for that scale's
complete spatial `σ`-algebra. -/
theorem measurableSet_biInter_eventFieldSigma [MeasurableSpace Ω]
    {E : Lattice d → Set Ω} {ι : Type*} (s : Finset ι) (u : ι → Lattice d) :
    MeasurableSet[eventFieldSigma E Set.univ] (⋂ i ∈ s, E (u i)) := by
  classical
  refine Finset.measurableSet_biInter s fun i _ => ?_
  exact measurableSet_event_of_mem (Set.mem_univ (u i))

/-- The intersection over a finite index set, grouped by the value of a scale
function. -/
theorem biInter_fiberwise {ι : Type*} [DecidableEq ι] (s : Finset ι) (j : ι → ℕ)
    (f : ι → Set Ω) :
    (⋂ t ∈ s.image j, ⋂ i ∈ s.filter (fun i => j i = t), f i) = ⋂ i ∈ s, f i := by
  ext ω
  simp only [Set.mem_iInter, Finset.mem_image, Finset.mem_filter]
  constructor
  · intro h i hi
    exact h (j i) ⟨i, hi, rfl⟩ i ⟨hi, rfl⟩
  · rintro h t - i ⟨hi, -⟩
    exact h i hi

/-- **The multiscale separated-product bound.**

For a finite family of events `E (j i) (u i)`, indexed by `i ∈ s`, whose sites
are pairwise farther apart than `Cdep * 3 ^ j` *whenever two members share the
scale `j`*, the measure of the intersection is the product of the measures.

No separation is required between members of different scales: that is exactly
what `IndependentEventScales` supplies. -/
theorem measure_biInter_multiscale_eq_prod [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω)
    (Cdep : ℕ) (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    {ι : Type*} (s : Finset ι) (j : ι → ℕ) (u : ι → Lattice d)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → j a = j b →
      Cdep * 3 ^ j a < latticeDist (u a) (u b)) :
    mu (⋂ i ∈ s, E (j i) (u i)) = ∏ i ∈ s, mu (E (j i) (u i)) := by
  classical
  -- inside one scale: the finite-range product formula
  have hfiber : ∀ t ∈ s.image j,
      mu (⋂ i ∈ s.filter (fun i => j i = t), E t (u i)) =
        ∏ i ∈ s.filter (fun i => j i = t), mu (E t (u i)) := by
    intro t _
    set S : Finset ι := s.filter (fun i => j i = t) with hS
    have hsep' : ∀ a b : {x // x ∈ S}, a ≠ b →
        Cdep * 3 ^ t < latticeDist (u a.1) (u b.1) := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have hane : a ≠ b := fun h => hab (Subtype.ext h)
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have := hsep a ha'.1 b hb'.1 hane (ha'.2.trans hb'.2.symm)
      rwa [ha'.2] at this
    have hkey := measure_biInter_event_eq_prod_of_finiteRange (μ := mu) (E := E t)
      (R := Cdep * 3 ^ t) (z := fun i : {x // x ∈ S} => u i.1) (hr t) hsep'
      (Finset.univ : Finset {x // x ∈ S})
    have hI : (⋂ i ∈ (Finset.univ : Finset {x // x ∈ S}), E t (u i.1)) =
        ⋂ i ∈ S, E t (u i) := by
      ext ω
      constructor
      · intro h
        exact Set.mem_iInter₂.mpr fun i hi =>
          Set.mem_iInter₂.mp h ⟨i, hi⟩ (Finset.mem_univ _)
      · intro h
        exact Set.mem_iInter₂.mpr fun i _ => Set.mem_iInter₂.mp h i.1 i.2
    have hP : (∏ i ∈ (Finset.univ : Finset {x // x ∈ S}), mu (E t (u i.1))) =
        ∏ i ∈ S, mu (E t (u i)) := by
      rw [← Finset.prod_attach S fun i => mu (E t (u i))]
      rfl
    rw [hI, hP] at hkey
    exact hkey
  -- across scales: independence of the complete spatial fields
  have hmaps : ∀ i ∈ s, j i ∈ s.image j := fun i hi => Finset.mem_image_of_mem j hi
  have hscale := hsc.meas_biInter (S := s.image j)
    (s := fun t => ⋂ i ∈ s.filter (fun i => j i = t), E t (u i))
    (fun t _ => measurableSet_biInter_eventFieldSigma
      (E := E t) (s.filter (fun i => j i = t)) u)
  have hfilter : ∀ t ∈ s.image j,
      (⋂ i ∈ s.filter (fun i => j i = t), E t (u i)) =
        ⋂ i ∈ s.filter (fun i => j i = t), E (j i) (u i) := by
    intro t _
    refine Set.iInter_congr fun i => ?_
    by_cases hi : i ∈ s.filter (fun i => j i = t)
    · rw [(Finset.mem_filter.mp hi).2]
    · simp [hi]
  calc mu (⋂ i ∈ s, E (j i) (u i))
      = mu (⋂ t ∈ s.image j, ⋂ i ∈ s.filter (fun i => j i = t), E t (u i)) := by
        rw [Set.iInter₂_congr hfilter, biInter_fiberwise s j fun i => E (j i) (u i)]
    _ = ∏ t ∈ s.image j, mu (⋂ i ∈ s.filter (fun i => j i = t), E t (u i)) := hscale
    _ = ∏ t ∈ s.image j, ∏ i ∈ s.filter (fun i => j i = t), mu (E t (u i)) :=
        Finset.prod_congr rfl hfiber
    _ = ∏ t ∈ s.image j, ∏ i ∈ s.filter (fun i => j i = t), mu (E (j i) (u i)) := by
        refine Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]
    _ = ∏ i ∈ s, mu (E (j i) (u i)) :=
        Finset.prod_fiberwise_of_maps_to hmaps _

/-- **The multiscale separated-product bound, as an upper estimate.**

The form the union bounds use: each factor is replaced by a scale-dependent
upper bound `p (j i)`. -/
theorem measure_biInter_multiscale_le_prod [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω)
    (Cdep : ℕ) (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    {ι : Type*} (s : Finset ι) (j : ι → ℕ) (u : ι → Lattice d) (p : ℕ → ENNReal)
    (hp : ∀ t z, mu (E t z) ≤ p t)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → j a = j b →
      Cdep * 3 ^ j a < latticeDist (u a) (u b)) :
    mu (⋂ i ∈ s, E (j i) (u i)) ≤ ∏ i ∈ s, p (j i) := by
  rw [measure_biInter_multiscale_eq_prod mu E Cdep hsc hr s j u hsep]
  exact Finset.prod_le_prod' fun i _ => hp (j i) (u i)

/-! ## Events supported on separated sets

The crossing certificates use *thickened* events — a scale-`j` event somewhere in
a ball of radius `r j` around a chosen centre — so the single-scale product
formula is needed for events supported on separated **sets**, not only at single
sites. -/

/-- The single-scale product formula for events measurable with respect to
separated spatial supports. -/
theorem measure_biInter_eq_prod_of_separated_supports [MeasurableSpace Ω]
    {mu : Measure Ω} [IsProbabilityMeasure mu] {F0 : Lattice d → Set Ω} {R : ℕ}
    {ι : Type*} (S : ι → Set (Lattice d)) (f : ι → Set Ω)
    (hindep : FiniteRangeIndependentEvents mu R F0)
    (hsep : ∀ a b : ι, a ≠ b → ∀ x ∈ S a, ∀ y ∈ S b, R < latticeDist x y) :
    ∀ s : Finset ι, (∀ i ∈ s, MeasurableSet[eventFieldSigma F0 (S i)] (f i)) →
      mu (⋂ i ∈ s, f i) = ∏ i ∈ s, mu (f i) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
      intro hf
      have hA : MeasurableSet[eventFieldSigma F0 (S a)] (f a) :=
        hf a (Finset.mem_insert_self a s)
      have hC : MeasurableSet[eventFieldSigma F0 (⋃ i ∈ (s : Set ι), S i)]
          (⋂ i ∈ s, f i) := by
        refine Finset.measurableSet_biInter s fun i hi => ?_
        exact (eventFieldSigma_mono F0 (fun x hx =>
          Set.mem_biUnion (Finset.mem_coe.mpr hi) hx)) _
            (hf i (Finset.mem_insert_of_mem hi))
      have hseparated : ∀ x ∈ S a, ∀ y ∈ (⋃ i ∈ (s : Set ι), S i),
          R < latticeDist x y := by
        intro x hx y hy
        obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp hy
        exact hsep a i (fun hai => ha (hai ▸ Finset.mem_coe.mp hi)) x hx y hy
      have hprod := (Indep_iff _ _ mu).mp (hindep _ _ hseparated) _ _ hA hC
      rw [Finset.set_biInter_insert, hprod, Finset.prod_insert ha,
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **The multiscale separated-product bound for thickened events.**

Each member of the family is an event supported on the ball of radius `r (j i)`
around `u i`; two members sharing a scale are required to be farther apart than
`2 * r j + Cdep * 3 ^ j`, so that their supports are separated by more than the
range of that scale. -/
theorem measure_biInter_multiscale_thickened_eq_prod [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω)
    (Cdep : ℕ) (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    {ι : Type*} (s : Finset ι) (j : ι → ℕ) (u : ι → Lattice d) (r : ℕ → ℕ)
    (f : ι → Set Ω)
    (hf : ∀ i ∈ s, MeasurableSet[eventFieldSigma (E (j i))
      (latticeBallFinset (u i) (r (j i)) : Set (Lattice d))] (f i))
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → j a = j b →
      2 * r (j a) + Cdep * 3 ^ j a < latticeDist (u a) (u b)) :
    mu (⋂ i ∈ s, f i) = ∏ i ∈ s, mu (f i) := by
  classical
  have hfiber : ∀ t ∈ s.image j,
      mu (⋂ i ∈ s.filter (fun i => j i = t), f i) =
        ∏ i ∈ s.filter (fun i => j i = t), mu (f i) := by
    intro t _
    set S : Finset ι := s.filter (fun i => j i = t) with hS
    have hsep' : ∀ a b : {x // x ∈ S}, a ≠ b →
        ∀ x ∈ (latticeBallFinset (u a.1) (r t) : Set (Lattice d)),
        ∀ y ∈ (latticeBallFinset (u b.1) (r t) : Set (Lattice d)),
          Cdep * 3 ^ t < latticeDist x y := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have hane : a ≠ b := fun h => hab (Subtype.ext h)
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have hd := hsep a ha'.1 b hb'.1 hane (ha'.2.trans hb'.2.symm)
      rw [ha'.2] at hd
      intro x hx y hy
      exact latticeDist_separated_balls hd (mem_latticeBallFinset_iff.mp hx)
        (mem_latticeBallFinset_iff.mp hy)
    have hmeas : ∀ i : {x // x ∈ S},
        MeasurableSet[eventFieldSigma (E t)
          (latticeBallFinset (u i.1) (r t) : Set (Lattice d))] (f i.1) := by
      rintro ⟨i, hi⟩
      have hi' := Finset.mem_filter.mp hi
      have := hf i hi'.1
      rw [hi'.2] at this
      exact this
    have hkey := measure_biInter_eq_prod_of_separated_supports (mu := mu) (F0 := E t)
      (R := Cdep * 3 ^ t)
      (S := fun i : {x // x ∈ S} => (latticeBallFinset (u i.1) (r t) : Set (Lattice d)))
      (f := fun i : {x // x ∈ S} => f i.1) (hr t) hsep'
      (Finset.univ : Finset {x // x ∈ S}) (fun i _ => hmeas i)
    have hI : (⋂ i ∈ (Finset.univ : Finset {x // x ∈ S}), f i.1) = ⋂ i ∈ S, f i := by
      ext ω
      constructor
      · intro h
        exact Set.mem_iInter₂.mpr fun i hi =>
          Set.mem_iInter₂.mp h ⟨i, hi⟩ (Finset.mem_univ _)
      · intro h
        exact Set.mem_iInter₂.mpr fun i _ => Set.mem_iInter₂.mp h i.1 i.2
    have hP : (∏ i ∈ (Finset.univ : Finset {x // x ∈ S}), mu (f i.1)) =
        ∏ i ∈ S, mu (f i) := by
      rw [← Finset.prod_attach S fun i => mu (f i)]
      rfl
    rw [hI, hP] at hkey
    exact hkey
  have hmaps : ∀ i ∈ s, j i ∈ s.image j := fun i hi => Finset.mem_image_of_mem j hi
  have hmeasScale : ∀ t ∈ s.image j,
      MeasurableSet[eventFieldSigma (E t) Set.univ]
        (⋂ i ∈ s.filter (fun i => j i = t), f i) := by
    intro t _
    refine Finset.measurableSet_biInter _ fun i hi => ?_
    have hi' := Finset.mem_filter.mp hi
    have hmi := hf i hi'.1
    rw [hi'.2] at hmi
    exact eventFieldSigma_mono (E t) (Set.subset_univ _) _ hmi
  have hscale := hsc.meas_biInter (S := s.image j)
    (s := fun t => ⋂ i ∈ s.filter (fun i => j i = t), f i) hmeasScale
  calc mu (⋂ i ∈ s, f i)
      = mu (⋂ t ∈ s.image j, ⋂ i ∈ s.filter (fun i => j i = t), f i) := by
        rw [biInter_fiberwise s j f]
    _ = ∏ t ∈ s.image j, mu (⋂ i ∈ s.filter (fun i => j i = t), f i) := hscale
    _ = ∏ t ∈ s.image j, ∏ i ∈ s.filter (fun i => j i = t), mu (f i) :=
        Finset.prod_congr rfl hfiber
    _ = ∏ i ∈ s, mu (f i) := Finset.prod_fiberwise_of_maps_to hmaps _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
