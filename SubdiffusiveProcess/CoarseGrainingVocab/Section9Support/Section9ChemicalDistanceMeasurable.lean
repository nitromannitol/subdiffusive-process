import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalDistance
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalGoodSiteDecoupling




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Good sites are the complement of the bad-site event. -/
theorem goodSite_eq_compl (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (u : Lattice d) :
    {ω : Ω | IsPercolationGoodSite E Cbox ω u} = (percolationBadSite E Cbox u)ᶜ := by
  ext ω
  simp [percolationBadSite]

theorem measurableSet_goodSite {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox : ℕ) (u : Lattice d) :
    MeasurableSet {ω : Ω | IsPercolationGoodSite E Cbox ω u} := by
  rw [goodSite_eq_compl]
  exact (measurableSet_percolationBadSite (Cbox := Cbox) _ hE u).compl

omit [MeasurableSpace Ω] in
/-- Reachability inside the **good** set is a countable union over the `J`-step
paths of finite intersections of good-site events. -/
theorem jStepReachableGood_eq_iUnion (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ)
    (v a : Lattice d) :
    {ω : Ω | JStepReachableIn J {u | IsPercolationGoodSite E Cbox ω u} v a} =
      ⋃ path ∈ {p : List (Lattice d) |
          p.head? = some v ∧ p.getLast? = some a ∧ IsJStepListPath J p},
        ⋂ u ∈ path, {ω : Ω | IsPercolationGoodSite E Cbox ω u} := by
  ext ω
  constructor
  · rintro ⟨path, h1, h2, h3, h4⟩
    exact Set.mem_iUnion₂.mpr ⟨path, ⟨h1, h2, h3⟩,
      Set.mem_iInter₂.mpr fun u hu => h4 u hu⟩
  · intro hω
    obtain ⟨path, ⟨h1, h2, h3⟩, h4⟩ := Set.mem_iUnion₂.mp hω
    exact ⟨path, h1, h2, h3, fun u hu => Set.mem_iInter₂.mp h4 u hu⟩

theorem measurableSet_jStepReachableGood {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox J : ℕ) (v a : Lattice d) :
    MeasurableSet
      {ω : Ω | JStepReachableIn J {u | IsPercolationGoodSite E Cbox ω u} v a} := by
  rw [jStepReachableGood_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun path _ => ?_
  exact MeasurableSet.biInter (Set.to_countable _) fun u _ =>
    measurableSet_goodSite hE Cbox u

omit [MeasurableSpace Ω] in
/-- Lying in a good component of diameter at least `R` is a countable union over
the pairs of component sites that realise the diameter. -/
theorem inGoodComponentOfDiameterAtLeast_eq_iUnion (E : ℕ → Lattice d → Set Ω)
    (Cbox J : ℕ) (R : ℝ) (v : Lattice d) :
    {ω : Ω | InGoodComponentOfDiameterAtLeast E Cbox J ω R v} =
      ⋃ ab ∈ {p : Lattice d × Lattice d | R ≤ (latticeDist p.1 p.2 : ℝ)},
        ({ω : Ω | IsPercolationGoodSite E Cbox ω v} ∩
          ({ω : Ω | JStepReachableIn J {u | IsPercolationGoodSite E Cbox ω u} v ab.1} ∩
            {ω : Ω |
              JStepReachableIn J {u | IsPercolationGoodSite E Cbox ω u} v ab.2})) := by
  ext ω
  constructor
  · rintro ⟨hgood, u, w, hu, hw, hdist⟩
    exact Set.mem_iUnion₂.mpr ⟨(u, w), hdist, hgood, hu, hw⟩
  · intro hω
    obtain ⟨ab, hab, hgood, hu, hw⟩ := Set.mem_iUnion₂.mp hω
    exact ⟨hgood, ab.1, ab.2, hu, hw, hab⟩

theorem measurableSet_inGoodComponentOfDiameterAtLeast
    {E : ℕ → Lattice d → Set Ω} (hE : ∀ j z, MeasurableSet (E j z))
    (Cbox J : ℕ) (R : ℝ) (v : Lattice d) :
    MeasurableSet {ω : Ω | InGoodComponentOfDiameterAtLeast E Cbox J ω R v} := by
  rw [inGoodComponentOfDiameterAtLeast_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun ab _ => ?_
  exact (measurableSet_goodSite hE Cbox v).inter
    ((measurableSet_jStepReachableGood hE Cbox J v ab.1).inter
      (measurableSet_jStepReachableGood hE Cbox J v ab.2))

omit [MeasurableSpace Ω] in
/-- A short good path is witnessed by one of countably many lists. -/
theorem isShortGoodPath_eq_iUnion (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (bound : ℝ) (v w : Lattice d) :
    {ω : Ω | IsShortGoodPath E Cbox ω bound v w} =
      ⋃ path ∈ {p : List (Lattice d) |
          p.head? = some v ∧ p.getLast? = some w ∧
            (p.length : ℝ) ≤ bound ∧ IsJStepListPath 1 p},
        ⋂ u ∈ path, {ω : Ω | IsPercolationGoodSite E Cbox ω u} := by
  ext ω
  constructor
  · rintro ⟨path, h1, h2, h3, h4, h5⟩
    exact Set.mem_iUnion₂.mpr ⟨path, ⟨h1, h2, h3, h4⟩,
      Set.mem_iInter₂.mpr fun u hu => h5 u hu⟩
  · intro hω
    obtain ⟨path, ⟨h1, h2, h3, h4⟩, h5⟩ := Set.mem_iUnion₂.mp hω
    exact ⟨path, h1, h2, h3, h4, fun u hu => Set.mem_iInter₂.mp h5 u hu⟩

theorem measurableSet_isShortGoodPath {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox : ℕ) (bound : ℝ) (v w : Lattice d) :
    MeasurableSet {ω : Ω | IsShortGoodPath E Cbox ω bound v w} := by
  rw [isShortGoodPath_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun path _ => ?_
  exact MeasurableSet.biInter (Set.to_countable _) fun u _ =>
    measurableSet_goodSite hE Cbox u

omit [MeasurableSpace Ω] in
/-- `D_L(z)` as a countable union over the pairs of endpoints realising it. -/
theorem chemicalDistanceFailureEvent_eq_iUnion (E : ℕ → Lattice d → Set Ω)
    (Cbox : ℕ) (Clen : ℝ) (z : Lattice d) (L : ℕ) :
    chemicalDistanceFailureEvent E Cbox Clen z L =
      ⋃ vw ∈ {p : Lattice d × Lattice d |
          InLatticeBallReal z p.1 L ∧ InLatticeBallReal z p.2 L},
        (({ω : Ω | InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) vw.1} ∩
            {ω : Ω |
              InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) vw.2}) ∩
          {ω : Ω | IsShortGoodPath E Cbox ω (Clen * L) vw.1 vw.2}ᶜ) := by
  ext ω
  constructor
  · rintro ⟨v, w, hv, hw, hvc, hwc, hpath⟩
    exact Set.mem_iUnion₂.mpr ⟨(v, w), ⟨hv, hw⟩, ⟨hvc, hwc⟩, hpath⟩
  · intro hω
    obtain ⟨vw, ⟨hv, hw⟩, ⟨hvc, hwc⟩, hpath⟩ := Set.mem_iUnion₂.mp hω
    exact ⟨vw.1, vw.2, hv, hw, hvc, hwc, hpath⟩

/-- **The chemical-distance failure event is measurable.** -/
theorem measurableSet_chemicalDistanceFailureEvent {E : ℕ → Lattice d → Set Ω}
    (hE : ∀ j z, MeasurableSet (E j z)) (Cbox : ℕ) (Clen : ℝ) (z : Lattice d)
    (L : ℕ) :
    MeasurableSet (chemicalDistanceFailureEvent E Cbox Clen z L) := by
  rw [chemicalDistanceFailureEvent_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun vw _ => ?_
  exact ((measurableSet_inGoodComponentOfDiameterAtLeast hE Cbox 1 _ vw.1).inter
    (measurableSet_inGoodComponentOfDiameterAtLeast hE Cbox 1 _ vw.2)).inter
    (measurableSet_isShortGoodPath hE Cbox _ vw.1 vw.2).compl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
