module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalPathConstruction

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The carrier -/



def badLevelEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (Clen : ℝ)
    (k : ℕ) (z : Lattice d) : Set Ω :=
  ⋃ L : ℕ, ⋃ _ : sqrtTwoScale k ≤ (L : ℝ), chemicalDistanceFailureEvent E Cbox Clen z L

theorem mem_badLevelEvent_iff {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ}
    {k : ℕ} {z : Lattice d} {ω : Ω} :
    ω ∈ badLevelEvent E Cbox Clen k z ↔
      ∃ L : ℕ, sqrtTwoScale k ≤ (L : ℝ) ∧
        ω ∈ chemicalDistanceFailureEvent E Cbox Clen z L := by
  simp [badLevelEvent]

/-- Above the level scale, absence of the level event is absence of the radius
event. -/
theorem not_mem_chemicalDistanceFailureEvent_of_not_mem_badLevelEvent
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {k : ℕ} {z : Lattice d}
    {ω : Ω} (h : ω ∉ badLevelEvent E Cbox Clen k z) {L : ℕ}
    (hL : sqrtTwoScale k ≤ (L : ℝ)) :
    ω ∉ chemicalDistanceFailureEvent E Cbox Clen z L :=
  fun hmem => h (mem_badLevelEvent_iff.mpr ⟨L, hL, hmem⟩)

/-- **`LevelToRadiusTransfer`, discharged by the carrier.** -/
theorem levelToRadiusTransfer_badLevelEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) :
    LevelToRadiusTransfer E Cbox Clen (badLevelEvent E Cbox Clen) := by
  intro z L k _ hLk ω hω
  exact mem_badLevelEvent_iff.mpr ⟨L, hLk, hω⟩

/-- The carrier is measurable as soon as every radius event is. -/
theorem measurableSet_badLevelEvent [MeasurableSpace Ω] {E : ℕ → Lattice d → Set Ω}
    {Cbox : ℕ} {Clen : ℝ} {k : ℕ} {z : Lattice d}
    (h : ∀ L : ℕ, MeasurableSet (chemicalDistanceFailureEvent E Cbox Clen z L)) :
    MeasurableSet (badLevelEvent E Cbox Clen k z) := by
  rw [badLevelEvent]
  exact MeasurableSet.iUnion fun L => MeasurableSet.iUnion fun _ => h L

theorem one_le_sqrtTwoScale (k : ℕ) : (1 : ℝ) ≤ sqrtTwoScale k := by
  rw [sqrtTwoScale]
  refine Real.one_le_exp ?_
  positivity

/-- A radius above a level scale is at least `1`, so the `1 ≤ L` side condition of
`LevelToRadiusTransfer` is automatic. -/
theorem one_le_of_sqrtTwoScale_le {k L : ℕ} (h : sqrtTwoScale k ≤ (L : ℝ)) : 1 ≤ L := by
  have h1 := (one_le_sqrtTwoScale k).trans h
  exact_mod_cast h1

theorem GoodWaypointChain.mono {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {ω : Ω} {steps steps' : ℕ} {link link' : ℝ} {z : Lattice d} {L : ℕ}
    (hs : steps ≤ steps') (hl : link ≤ link')
    (h : GoodWaypointChain E Cbox ω steps link z L) :
    GoodWaypointChain E Cbox ω steps' link' z L := by
  intro v w hv hw hvc hwc
  obtain ⟨x, n, hn, hns, hx0, hxn, hlink⟩ := h v w hv hw hvc hwc
  exact ⟨x, n, hn, hns.trans hs, hx0, hxn, fun i hi => (hlink i hi).mono hl⟩

/-! ## The carrier is decreasing in the level -/

theorem one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  simp

theorem sqrtTwoScale_mono {j k : ℕ} (hjk : j ≤ k) : sqrtTwoScale j ≤ sqrtTwoScale k :=
  Real.exp_le_exp.mpr (pow_le_pow_right₀ one_le_sqrt_two hjk)

/-- Higher levels ask for failures at larger radii, so the events shrink. -/
theorem badLevelEvent_antitone {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ}
    {j k : ℕ} (hjk : j ≤ k) (z : Lattice d) :
    badLevelEvent E Cbox Clen k z ⊆ badLevelEvent E Cbox Clen j z := by
  intro ω hω
  obtain ⟨L, hL, hmem⟩ := mem_badLevelEvent_iff.mp hω
  exact mem_badLevelEvent_iff.mpr ⟨L, (sqrtTwoScale_mono hjk).trans hL, hmem⟩

/-! ## The routing datum, and the forcing inclusion for the carrier -/



def ClusterAvoidingWaypoints (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (Clen : ℝ)
    (Bad : Lattice d → Set Ω) (Lk : ℝ) (R : ℕ) (S : Finset (Lattice d))
    (Cross : Set Ω) (steps : ℕ) (link : ℝ) (x : Lattice d) (L : ℕ) : Prop :=
  ∀ ω : Ω, ω ∉ Cross →
    (∀ y ∈ S, ∀ u ∈ S, ω ∈ Bad y → ω ∈ Bad u → latticeDist y u ≤ R) →
    ∀ v w : Lattice d,
      InLatticeBallReal x v L → InLatticeBallReal x w L →
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) v →
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) w →
      ∃ p : ℕ → Lattice d, ∃ n : ℕ, 0 < n ∧ n ≤ steps ∧ p 0 = v ∧ p n = w ∧
        ∀ i, i < n → ∃ y ∈ S, ∃ M : ℕ, ω ∉ Bad y ∧ Lk ≤ (M : ℝ) ∧
          Clen * M ≤ link ∧
          InLatticeBallReal y (p i) M ∧ InLatticeBallReal y (p (i + 1)) M ∧
          InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((M : ℝ) / 20) (p i) ∧
          InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((M : ℝ) / 20) (p (i + 1))

/-- **One link.**  A waypoint pair co-located in a good level-`k` box is joined
by a good path of at most `link` vertices. -/
theorem isShortGoodPath_of_not_mem_badLevelEvent
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen link : ℝ} {k : ℕ} {ω : Ω}
    {y : Lattice d} {M : ℕ} (hy : ω ∉ badLevelEvent E Cbox Clen k y)
    (hM : sqrtTwoScale k ≤ (M : ℝ)) (hlink : Clen * M ≤ link)
    {a b : Lattice d}
    (ha : InLatticeBallReal y a M) (hb : InLatticeBallReal y b M)
    (hac : InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((M : ℝ) / 20) a)
    (hbc : InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((M : ℝ) / 20) b) :
    IsShortGoodPath E Cbox ω link a b := by
  have hnot := not_mem_chemicalDistanceFailureEvent_of_not_mem_badLevelEvent hy hM
  by_contra hcon
  exact hnot ⟨a, b, ha, hb, hac, hbc, fun hshort => hcon (hshort.mono hlink)⟩

/-- **The waypoint datum produces the `GoodWaypointChain` of
`Section9ChemicalPathConstruction`.** -/
theorem goodWaypointChain_of_clusterAvoidingWaypoints
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen link : ℝ} {k R steps : ℕ}
    {S : Finset (Lattice d)} {Cross : Set Ω} {x : Lattice d} {L : ℕ} {ω : Ω}
    (hdatum : ClusterAvoidingWaypoints E Cbox Clen (badLevelEvent E Cbox Clen k)
      (sqrtTwoScale k) R S Cross steps link x L)
    (hcross : ω ∉ Cross)
    (hcluster : ∀ y ∈ S, ∀ u ∈ S, ω ∈ badLevelEvent E Cbox Clen k y →
      ω ∈ badLevelEvent E Cbox Clen k u → latticeDist y u ≤ R) :
    GoodWaypointChain E Cbox ω steps link x L := by
  intro v w hv hw hvc hwc
  obtain ⟨p, n, hn, hns, hp0, hpn, hlinks⟩ := hdatum ω hcross hcluster v w hv hw hvc hwc
  refine ⟨p, n, hn, hns, hp0, hpn, fun i hi => ?_⟩
  obtain ⟨y, -, M, hyb, hM, hlink, hai, hbi, haci, hbci⟩ := hlinks i hi
  exact isShortGoodPath_of_not_mem_badLevelEvent hyb hM hlink hai hbi haci hbci

/-- **`ClusteredBadForcing` for the level carrier.**

Given, at every radius above the level scale `L_{k+1}`, a waypoint datum whose
total budget `steps * link` fits in `Clen * L`, the level carrier satisfies the
forcing inclusion that the `√2` renormalization consumes. -/
theorem clusteredBadForcing_badLevelEvent
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {k R : ℕ}
    {S : Finset (Lattice d)} {Cross : Set Ω} {x : Lattice d}
    (hroute : ∀ L : ℕ, sqrtTwoScale (k + 1) ≤ (L : ℝ) →
      ∃ steps : ℕ, ∃ link : ℝ, 0 ≤ link ∧ (steps : ℝ) * link ≤ Clen * L ∧
        ClusterAvoidingWaypoints E Cbox Clen (badLevelEvent E Cbox Clen k)
          (sqrtTwoScale k) R S Cross steps link x L) :
    ClusteredBadForcing (badLevelEvent E Cbox Clen k)
      (badLevelEvent E Cbox Clen (k + 1) x) Cross R S := by
  intro ω hcross hcluster hmem
  obtain ⟨L, hL, hfail⟩ := mem_badLevelEvent_iff.mp hmem
  obtain ⟨steps, link, hlink0, hbudget, hdatum⟩ := hroute L hL
  exact not_mem_chemicalDistanceFailureEvent_of_goodWaypointChain hlink0 hbudget
    (goodWaypointChain_of_clusterAvoidingWaypoints hdatum hcross hcluster) hfail


/-! ## The windowed carrier

The carrier `badLevelEvent` above is an **unbounded** union: `Bad k z` involves the
field in balls `B_L(z)` of every radius `L ≥ L_k`.  That is fatal for the
finite-range independence hypothesis `hindep` of the level induction, which asks
for `FiniteRangeIndependentEvents mu (Rk k) (Bad k)` at a range `Rk k` that the
routing needs to keep **below** `L_k`
(`Section9ChemicalForcing.badIndex_unique_of_quasiGeodesic`).

The level selection actually available is two-sided:
`Section9ChemicalRenormalization.exists_sqrtTwo_level` returns a level `k` with
`L_k ≤ L < L_{k+1}`, not merely `L_k ≤ L`. This permits a **windowed** union of
radii. It does not give bounded spatial support: goodness still involves all
event scales and their influence boxes, and the component predicate is global.

`Section9ChemicalLocalCarrier` now supplies actual truncated site events and a
recursive separated-pair carrier, with proved support and dependence radii.
The transfer from that carrier to chemical-distance failures and the bounded-cost
routing still need to be proved. The windowed carrier below retains its direct
radius-transfer and seed estimates; its exact independence is not derived. -/

/-- **The windowed level-`k` unfavourable event**: chemical-distance failures at
radii in the single schedule window `[L_k, L_{k+1})`. -/
def badWindowEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (Clen : ℝ)
    (k : ℕ) (z : Lattice d) : Set Ω :=
  ⋃ L : ℕ, ⋃ _ : sqrtTwoScale k ≤ (L : ℝ) ∧ (L : ℝ) < sqrtTwoScale (k + 1),
    chemicalDistanceFailureEvent E Cbox Clen z L

theorem mem_badWindowEvent_iff {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ}
    {k : ℕ} {z : Lattice d} {ω : Ω} :
    ω ∈ badWindowEvent E Cbox Clen k z ↔
      ∃ L : ℕ, (sqrtTwoScale k ≤ (L : ℝ) ∧ (L : ℝ) < sqrtTwoScale (k + 1)) ∧
        ω ∈ chemicalDistanceFailureEvent E Cbox Clen z L := by
  simp [badWindowEvent]

theorem not_mem_chemicalDistanceFailureEvent_of_not_mem_badWindowEvent
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {k : ℕ} {z : Lattice d}
    {ω : Ω} (h : ω ∉ badWindowEvent E Cbox Clen k z) {L : ℕ}
    (hL : sqrtTwoScale k ≤ (L : ℝ)) (hL' : (L : ℝ) < sqrtTwoScale (k + 1)) :
    ω ∉ chemicalDistanceFailureEvent E Cbox Clen z L := fun hmem =>
  h (mem_badWindowEvent_iff.mpr ⟨L, ⟨hL, hL'⟩, hmem⟩)

/-- **The windowed level-to-radius transfer.**  Only the radii of the level's own
window have to be dominated — which is exactly what the two-sided level selection
`exists_sqrtTwo_level` delivers. -/
def LevelToRadiusWindowTransfer (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (Clen : ℝ)
    (Bad : ℕ → Lattice d → Set Ω) : Prop :=
  ∀ (z : Lattice d) (L k : ℕ), sqrtTwoScale k ≤ (L : ℝ) → (L : ℝ) < sqrtTwoScale (k + 1) →
    chemicalDistanceFailureEvent E Cbox Clen z L ⊆ Bad k z

/-- The windowed carrier discharges the windowed transfer definitionally. -/
theorem levelToRadiusWindowTransfer_badWindowEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) :
    LevelToRadiusWindowTransfer E Cbox Clen (badWindowEvent E Cbox Clen) := by
  intro z L k hL hL' ω hω
  exact mem_badWindowEvent_iff.mpr ⟨L, ⟨hL, hL'⟩, hω⟩

/-- The windowed routing datum: as `ClusterAvoidingWaypoints`, but each link radius
`M` must stay in the level's own window `[L_k, L_{k+1})`. -/
def ClusterAvoidingWindowWaypoints (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (Clen : ℝ)
    (Bad : Lattice d → Set Ω) (Lk Lk' : ℝ) (R : ℕ) (S : Finset (Lattice d))
    (Cross : Set Ω) (steps : ℕ) (link : ℝ) (x : Lattice d) (L : ℕ) : Prop :=
  ∀ ω : Ω, ω ∉ Cross →
    (∀ y ∈ S, ∀ u ∈ S, ω ∈ Bad y → ω ∈ Bad u → latticeDist y u ≤ R) →
    ∀ v w : Lattice d,
      InLatticeBallReal x v L → InLatticeBallReal x w L →
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) v →
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) w →
      ∃ p : ℕ → Lattice d, ∃ n : ℕ, 0 < n ∧ n ≤ steps ∧ p 0 = v ∧ p n = w ∧
        ∀ i, i < n → ∃ y ∈ S, ∃ M : ℕ, ω ∉ Bad y ∧ Lk ≤ (M : ℝ) ∧ (M : ℝ) < Lk' ∧
          Clen * M ≤ link ∧
          InLatticeBallReal y (p i) M ∧ InLatticeBallReal y (p (i + 1)) M ∧
          InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((M : ℝ) / 20) (p i) ∧
          InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((M : ℝ) / 20) (p (i + 1))

theorem goodWaypointChain_of_clusterAvoidingWindowWaypoints
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen link : ℝ} {k R steps : ℕ}
    {S : Finset (Lattice d)} {Cross : Set Ω} {x : Lattice d} {L : ℕ} {ω : Ω}
    (hdatum : ClusterAvoidingWindowWaypoints E Cbox Clen (badWindowEvent E Cbox Clen k)
      (sqrtTwoScale k) (sqrtTwoScale (k + 1)) R S Cross steps link x L)
    (hcross : ω ∉ Cross)
    (hcluster : ∀ y ∈ S, ∀ u ∈ S, ω ∈ badWindowEvent E Cbox Clen k y →
      ω ∈ badWindowEvent E Cbox Clen k u → latticeDist y u ≤ R) :
    GoodWaypointChain E Cbox ω steps link x L := by
  intro v w hv hw hvc hwc
  obtain ⟨p, n, hn, hns, hp0, hpn, hlinks⟩ := hdatum ω hcross hcluster v w hv hw hvc hwc
  refine ⟨p, n, hn, hns, hp0, hpn, fun i hi => ?_⟩
  obtain ⟨y, -, M, hyb, hM, hM', hlink, hai, hbi, haci, hbci⟩ := hlinks i hi
  have hnot := not_mem_chemicalDistanceFailureEvent_of_not_mem_badWindowEvent hyb hM hM'
  by_contra hcon
  exact hnot ⟨p i, p (i + 1), hai, hbi, haci, hbci,
    fun hshort => hcon (hshort.mono hlink)⟩

/-- **`ClusteredBadForcing` for the windowed carrier.** -/
theorem clusteredBadForcing_badWindowEvent
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Clen : ℝ} {k R : ℕ}
    {S : Finset (Lattice d)} {Cross : Set Ω} {x : Lattice d}
    (hroute : ∀ L : ℕ, sqrtTwoScale (k + 1) ≤ (L : ℝ) → (L : ℝ) < sqrtTwoScale (k + 2) →
      ∃ steps : ℕ, ∃ link : ℝ, 0 ≤ link ∧ (steps : ℝ) * link ≤ Clen * L ∧
        ClusterAvoidingWindowWaypoints E Cbox Clen (badWindowEvent E Cbox Clen k)
          (sqrtTwoScale k) (sqrtTwoScale (k + 1)) R S Cross steps link x L) :
    ClusteredBadForcing (badWindowEvent E Cbox Clen k)
      (badWindowEvent E Cbox Clen (k + 1) x) Cross R S := by
  intro ω hcross hcluster hmem
  obtain ⟨L, ⟨hL, hL'⟩, hfail⟩ := mem_badWindowEvent_iff.mp hmem
  obtain ⟨steps, link, hlink0, hbudget, hdatum⟩ := hroute L hL hL'
  exact not_mem_chemicalDistanceFailureEvent_of_goodWaypointChain hlink0 hbudget
    (goodWaypointChain_of_clusterAvoidingWindowWaypoints hdatum hcross hcluster) hfail

theorem sqrtTwoScale_lt_succ (k : ℕ) : sqrtTwoScale k < sqrtTwoScale (k + 1) := by
  rw [sqrtTwoScale, sqrtTwoScale]
  refine Real.exp_lt_exp.mpr ?_
  rw [pow_succ]
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
      Real.sqrt_nonneg (2:ℝ), one_le_sqrt_two]
  have hpos : (0 : ℝ) < Real.sqrt 2 ^ k := by positivity
  nlinarith

theorem measurableSet_badWindowEvent [MeasurableSpace Ω] {E : ℕ → Lattice d → Set Ω}
    {Cbox : ℕ} {Clen : ℝ} {k : ℕ} {z : Lattice d}
    (h : ∀ L : ℕ, MeasurableSet (chemicalDistanceFailureEvent E Cbox Clen z L)) :
    MeasurableSet (badWindowEvent E Cbox Clen k z) := by
  rw [badWindowEvent]
  exact MeasurableSet.iUnion fun L => MeasurableSet.iUnion fun _ => h L

theorem badWindowEvent_subset_badLevelEvent {E : ℕ → Lattice d → Set Ω}
    {Cbox : ℕ} {Clen : ℝ} (k : ℕ) (z : Lattice d) :
    badWindowEvent E Cbox Clen k z ⊆ badLevelEvent E Cbox Clen k z := by
  intro ω hω
  obtain ⟨L, ⟨hL, -⟩, hmem⟩ := mem_badWindowEvent_iff.mp hω
  exact mem_badLevelEvent_iff.mpr ⟨L, hL, hmem⟩

/-! ## The windowed level selection, and the chemical bound -/

/-- The two-sided level selection with the `q`-uniform rate attached. -/
theorem exists_window_level_bound {a Centropy : ℝ} {dim : ℕ}
    (ha : 0 < a) (hC : 1 ≤ Centropy)
    (hq0 : 2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * dim ≤ a)
    {L : ℝ} (hL : Real.exp 1 ≤ L) :
    ∃ k : ℕ, sqrtTwoScale k ≤ L ∧ L < sqrtTwoScale (k + 1) ∧
      sqrtTwoLevelBound a Centropy dim k ≤ Real.exp (-(a / 4 * Real.log L ^ 2)) := by
  obtain ⟨k, hle, hlt⟩ := exists_sqrtTwo_level L hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hL
  have hstep := exp_neg_two_pow_le_exp_neg_log_sq (b := a / 2) (k := k)
    (by linarith) hL1 hlt
  refine ⟨k, hle, hlt, ?_⟩
  refine (sqrtTwoLevelBound_le_exp_neg_half ha hC hq0 k).trans (hstep.trans (le_of_eq ?_))
  congr 1
  ring

/-- **The chemical-distance estimate from the windowed carrier.**  Same conclusion as
`Section9ChemicalAssembly.measure_chemicalDistanceFailureEvent_le`, from the *windowed*
transfer. -/
theorem measure_chemicalDistanceFailureEvent_le_window [MeasurableSpace Ω]
    {mu : Measure Ω} [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {Bad Cross : ℕ → Lattice d → Set Ω} {Rk : ℕ → ℕ}
    {Sk : ℕ → Lattice d → Finset (Lattice d)} {Clen c Cfail q Centropy : ℝ}
    {dim : ℕ}
    (hq : 0 < q) (hc : 0 < c) (hCfail : 1 ≤ Cfail) (hCentropy : 1 ≤ Centropy)
    (hq0 : 2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * dim ≤ 4 * c * q)
    (hseed : ∀ x, mu (Bad 0 x) ≤ ENNReal.ofReal (Real.exp (-(4 * c * q))))
    (hindep : ∀ k, FiniteRangeIndependentEvents mu (Rk k) (Bad k))
    (hcross : ∀ k x, mu (Cross k x) ≤
      ENNReal.ofReal (Real.exp (-(4 * c * q * Real.exp (3 / 2 * Real.sqrt 2 ^ k)))))
    (hcard : ∀ k x, (((separatedPairs (Rk k) (Sk k x)).card : ℕ) : ℝ) ≤
      Real.exp (sqrtTwoScheduleEntropy Centropy dim k))
    (hforce : ∀ k x,
      ClusteredBadForcing (Bad k) (Bad (k + 1) x) (Cross k x) (Rk k) (Sk k x))
    (htransfer : LevelToRadiusWindowTransfer E Cbox Clen Bad)
    (hsmall : SmallRadiusBound mu E Cbox Clen c Cfail q)
    (z : Lattice d) (L : ℕ) (hL : 1 ≤ L) :
    mu (chemicalDistanceFailureEvent E Cbox Clen z L) ≤
      ENNReal.ofReal (Cfail * Real.exp (-c * q * Real.log L ^ 2)) := by
  rcases lt_or_ge (L : ℝ) (Real.exp 1) with hsmallL | hbigL
  · exact hsmall z L hL hsmallL
  · have ha : 0 < 4 * c * q := by positivity
    obtain ⟨k, hlevel, hlevel', hbound⟩ :=
      exists_window_level_bound (dim := dim) ha hCentropy hq0 hbigL
    have hmeas := measure_le_sqrtTwoLevelBound (Bad := Bad) (Cross := Cross)
      (Rk := Rk) (Sk := Sk) (dim := dim) hCentropy hseed hindep hcross hcard hforce k z
    refine (measure_mono (htransfer z L k hlevel hlevel')).trans (hmeas.trans ?_)
    refine ENNReal.ofReal_le_ofReal (hbound.trans ?_)
    have heq : 4 * c * q / 4 * Real.log L ^ 2 = c * q * Real.log L ^ 2 := by ring
    rw [heq]
    have h1 : Real.exp (-(c * q * Real.log L ^ 2)) =
        Real.exp (-c * q * Real.log L ^ 2) := by ring_nf
    rw [h1]
    nlinarith [Real.exp_pos (-c * q * Real.log L ^ 2)]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
