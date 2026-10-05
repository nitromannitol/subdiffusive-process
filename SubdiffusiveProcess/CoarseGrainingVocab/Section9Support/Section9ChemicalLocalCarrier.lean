module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalP346Ergodicity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalRenormalizationStep

@[expose] public section

/-!
# Local site fields and recursive separated-pair events

`truncatedBadSite` retains finitely many original event scales. Its dependence
range is proved from independence across scales and the original per-scale
finite-range hypotheses. The omitted scales are recorded explicitly by
`percolationBadSite_subset_truncated_union_tail`.

`recursivePairEvent` is the recursive unfavorable event of DRS (3.3). Its
support radius is the seed support radius plus the sum of child-cover radii.
The corresponding finite-range theorem is an exact subfamily independence
statement. These locality results do not assert a transfer from recursive
unfavorable events to chemical-distance failures.

Sources: `mfd:in-deterministic` and `s.tightness` and
Drewitz--Ráth--Sapozhnikov, arXiv:1212.2885, (3.3).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open MeasureTheory Set ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal
noncomputable section
theorem eventFieldSigma_le_of_measurable {d : ℕ} {Ω : Type*}
 (E : Lattice d → Set Ω) (S : Set (Lattice d)) (m : MeasurableSpace Ω)
 (h : ∀ x ∈ S, MeasurableSet[m] (E x)) : eventFieldSigma E S ≤ m := by
  unfold eventFieldSigma
  refine MeasurableSpace.generateFrom_le ?_
  rintro A ⟨x, hx, rfl⟩
  exact h x hx

theorem latticeThickening_separated {d r R : ℕ} {S T : Set (Lattice d)}
 (h : ∀ x ∈ S, ∀ y ∈ T, 2*r+R < latticeDist x y) :
 ∀ u ∈ (⋃ x ∈ S, (latticeBallFinset x r : Set (Lattice d))),
 ∀ v ∈ (⋃ y ∈ T, (latticeBallFinset y r : Set (Lattice d))), R < latticeDist u v := by
  intro u hu v hv
  obtain ⟨x, hx, hu'⟩ := Set.mem_iUnion₂.mp hu
  obtain ⟨y, hy, hv'⟩ := Set.mem_iUnion₂.mp hv
  have hu2 : latticeDist x u ≤ r := mem_latticeBallFinset_iff.mp hu'
  have hv2 : latticeDist y v ≤ r := mem_latticeBallFinset_iff.mp hv'
  exact latticeDist_separated_balls (h x hx y hy) hu2 hv2

theorem measurableSet_pairEvent {d : ℕ} {Ω : Type*} (m : MeasurableSpace Ω)
 (F : Lattice d → Set Ω) (R : ℕ) (S : Finset (Lattice d))
 (h : ∀ x ∈ S, MeasurableSet[m] (F x)) :
 MeasurableSet[m] (⋃ yz ∈ separatedPairs R S, F yz.1 ∩ F yz.2) := by
 refine MeasurableSet.biUnion (separatedPairs R S).countable_toSet ?_
 intro yz hyz
 have hp := Finset.mem_product.mp (Finset.mem_filter.mp hyz).1
 exact (h yz.1 hp.1).inter (h yz.2 hp.2)

theorem pairEvent_subset_seedUnion {d : ℕ} {Ω : Type*}
    (F : Lattice d → Set Ω) (R : ℕ) (S : Finset (Lattice d)) :
    (⋃ yz ∈ separatedPairs R S, F yz.1 ∩ F yz.2) ⊆ ⋃ x ∈ S, F x := by
  intro z hz
  obtain ⟨yz, hyz, hzF⟩ := Set.mem_iUnion₂.mp hz
  have hyz' : yz ∈ S ×ˢ S := (Finset.mem_filter.mp hyz).1
  have h1 : yz.1 ∈ S := (Finset.mem_product.mp hyz').1
  exact Set.mem_iUnion₂.mpr ⟨yz.1, h1, hzF.1⟩

theorem latticeBallFinset_subset_thickening {d r : ℕ} {S : Set (Lattice d)}
  {x : Lattice d} (hx : x ∈ S) :
  (latticeBallFinset x r : Set (Lattice d)) ⊆ ⋃ y ∈ S, (latticeBallFinset y r : Set (Lattice d)) := by
  intro u hu
  exact Set.mem_iUnion₂.mpr ⟨x, hx, hu⟩

theorem latticeBallFinset_subset_of_centres {d r s : ℕ} {x y : Lattice d}
 (hy : y ∈ latticeBallFinset x r) :
 (latticeBallFinset y s : Set (Lattice d)) ⊆ (latticeBallFinset x (r+s) : Set (Lattice d)) := by
  intro u hu
  change u ∈ latticeBallFinset y s at hu
  change u ∈ latticeBallFinset x (r+s)
  rw [mem_latticeBallFinset_iff] at hy hu ⊢
  calc latticeDist x u ≤ latticeDist x y + latticeDist y u := latticeDist_triangle x y u
    _ ≤ r + s := add_le_add hy hu

theorem supportRadius_step (step : ℕ → ℕ) (k : ℕ) :
 (∑ i ∈ Finset.range (k+1), step i) = (∑ i ∈ Finset.range k, step i) + step k := by
 simp only [Finset.sum_range_succ]

theorem measure_pairEvent_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
 (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Lattice d → Set Ω)
 (R : ℕ) (S : Finset (Lattice d)) (p : ℝ≥0∞)
 (hi : FiniteRangeIndependentEvents μ R F) (hp : ∀ x, μ (F x) ≤ p) :
 μ (⋃ yz ∈ separatedPairs R S, F yz.1 ∩ F yz.2) ≤ (separatedPairs R S).card * p^2 := by
  calc μ (⋃ yz ∈ separatedPairs R S, F yz.1 ∩ F yz.2)
      ≤ ∑ yz ∈ separatedPairs R S, μ (F yz.1 ∩ F yz.2) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _yz ∈ separatedPairs R S, p^2 :=
        Finset.sum_le_sum fun yz hyz => by
          rw [measure_inter_event_eq_mul_of_finiteRange hi
            (separated_of_mem_separatedPairs hyz), pow_two]
          exact mul_le_mul' (hp _) (hp _)
    _ = (separatedPairs R S).card * p^2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Local functions of a finite-range field have the enlarged dependence range. -/
theorem finiteRangeIndependentEvents_of_local_measurable {d R r : ℕ} {Ω : Type*}
 [MeasurableSpace Ω] (μ : Measure Ω) (E F : Lattice d → Set Ω)
 (hi : FiniteRangeIndependentEvents μ R E)
 (hloc : ∀ x, MeasurableSet[eventFieldSigma E (latticeBallFinset x r : Set (Lattice d))] (F x)) :
 FiniteRangeIndependentEvents μ (2*r+R) F := by
  intro S T hsep
  have key := hi (⋃ x ∈ S, (latticeBallFinset x r : Set (Lattice d)))
    (⋃ x ∈ T, (latticeBallFinset x r : Set (Lattice d)))
    (latticeThickening_separated hsep)
  exact indep_of_subsigmas μ key
    (eventFieldSigma_le_of_measurable F S _ fun x hx =>
      (eventFieldSigma_mono E (latticeBallFinset_subset_thickening hx)) _ (hloc x))
    (eventFieldSigma_le_of_measurable F T _ fun x hx =>
      (eventFieldSigma_mono E (latticeBallFinset_subset_thickening hx)) _ (hloc x))

/-- The bad-site event after retaining the event scales through `j0`. -/
def truncatedBadSite {d : ℕ} {Ω : Type*}
    (E : ℕ → Lattice d → Set Ω) (Cbox j0 : ℕ) (z : Lattice d) : Set Ω :=
  ⋃ j ∈ Finset.range (j0+1), influenceFailure (E j) (Cbox*3^j) z

/-- An unfavorable parent contains two separated unfavorable children. -/
def recursivePairEvent {d : ℕ} {Ω : Type*} (Seed : Lattice d → Set Ω)
    (R : ℕ → ℕ) (S : ℕ → Lattice d → Finset (Lattice d)) : ℕ → Lattice d → Set Ω
  | 0, x => Seed x
  | k+1, x => ⋃ yz ∈ separatedPairs (R k) (S k x),
      recursivePairEvent Seed R S k yz.1 ∩ recursivePairEvent Seed R S k yz.2

/-- The bad-site event after retaining the event scales through `j0`. -/
theorem truncatedBadSite_subset {d Cbox j0 : ℕ} {Ω : Type*}
    (E : ℕ → Lattice d → Set Ω) (z : Lattice d) :
    truncatedBadSite E Cbox j0 z ⊆ percolationBadSite E Cbox z := by
  intro x hx
  simp only [truncatedBadSite, Set.mem_iUnion₂] at hx
  obtain ⟨j, _hj, hx⟩ := hx
  rw [percolationBadSite_eq_iUnion]
  exact Set.mem_iUnion.mpr ⟨j, hx⟩

theorem percolationBadSite_subset_truncated_union_tail {d Cbox j0 : ℕ} {Ω : Type*}
 (E : ℕ → Lattice d → Set Ω) (z : Lattice d) :
 percolationBadSite E Cbox z ⊆ truncatedBadSite E Cbox j0 z ∪ highLevelInfluence E Cbox j0 z := by
 intro x hx
 rw [percolationBadSite_eq_iUnion E Cbox z] at hx
 obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
 by_cases h : j ≤ j0
 · refine Set.mem_union_left _ ?_
   exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by omega), hj⟩
 · refine Set.mem_union_right _ ?_
   refine Set.mem_iUnion.mpr ⟨j - j0 - 1, ?_⟩
   have hj' : j - j0 - 1 + j0 + 1 = j := by omega
   rw [hj']
   exact hj

/-- The exact accumulated support radius of the recursive carrier. -/
theorem measurableSet_recursivePairEvent {d r : ℕ} {Ω : Type*}
 (E Seed : Lattice d → Set Ω) (R step : ℕ → ℕ)
 (S : ℕ → Lattice d → Finset (Lattice d))
 (hs : ∀ k x, S k x ⊆ latticeBallFinset x (step k))
 (hseed : ∀ x, MeasurableSet[eventFieldSigma E (latticeBallFinset x r : Set (Lattice d))] (Seed x)) :
 ∀ k x, MeasurableSet[eventFieldSigma E
   (latticeBallFinset x (r + ∑ i∈Finset.range k,step i) : Set (Lattice d))]
   (recursivePairEvent Seed R S k x) := by
  intro k
  induction k with
  | zero =>
    intro x
    simpa [recursivePairEvent] using! hseed x
  | succ k ih =>
    intro x
    rw [recursivePairEvent, Finset.sum_range_succ]
    refine measurableSet_pairEvent _ _ _ _ ?_
    intro y hy
    have hb := latticeBallFinset_subset_of_centres
      (s := r + ∑ i ∈ Finset.range k, step i) (hs k x hy)
    have hsub : (latticeBallFinset y (r + ∑ i ∈ Finset.range k, step i) : Set (Lattice d)) ⊆
        (latticeBallFinset x (r + ((∑ i ∈ Finset.range k, step i) + step k)) : Set (Lattice d)) := by
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hb
    exact (eventFieldSigma_mono E hsub) _ (ih y)

theorem not_mem_pairEvent_iff_clustered {d : ℕ} {Ω : Type*}
    (F : Lattice d → Set Ω) (R : ℕ) (S : Finset (Lattice d)) (ω : Ω) :
    ω ∉ (⋃ yz ∈ separatedPairs R S, F yz.1 ∩ F yz.2) ↔
      (∀ x ∈ S, ω ∈ F x → ∀ y ∈ S, ω ∈ F y → latticeDist x y ≤ R) := by
  constructor
  · intro h x hx hfx y hy hfy
    by_contra hgt
    exact h (Set.mem_iUnion₂.mpr ⟨(x, y),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, Nat.lt_of_not_ge hgt⟩,
      hfx, hfy⟩)
  · intro h hw
    obtain ⟨yz, hyz, hmem⟩ := Set.mem_iUnion₂.mp hw
    obtain ⟨hprod, hlt⟩ := Finset.mem_filter.mp hyz
    obtain ⟨hfx, hfy⟩ := hmem
    exact absurd hlt (Nat.not_lt.mpr (h yz.1 (Finset.mem_product.mp hprod).1 hfx
      yz.2 (Finset.mem_product.mp hprod).2 hfy))

theorem measurableSet_truncatedBadSite {d Cbox j0 : ℕ} {Ω : Type*}
 (E : ℕ → Lattice d → Set Ω) (z : Lattice d) :
 MeasurableSet[⨆ j∈Finset.range (j0+1),eventFieldSigma (E j)
   (latticeBallFinset z (Cbox*3^j0) : Set (Lattice d))] (truncatedBadSite E Cbox j0 z)  := by
  unfold truncatedBadSite influenceFailure
  refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun hj =>
    MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun hu => ?_
  have hjle : j ≤ j0 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hrad : Cbox*3^j ≤ Cbox*3^j0 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hjle)
  have hu' : u ∈ (latticeBallFinset z (Cbox*3^j0) : Set (Lattice d)) :=
    mem_latticeBallFinset_iff.mpr ((mem_latticeBallFinset_iff.mp hu).trans hrad)
  have hm : eventFieldSigma (E j) (latticeBallFinset z (Cbox*3^j0) : Set (Lattice d)) ≤
      ⨆ j ∈ Finset.range (j0+1), eventFieldSigma (E j)
        (latticeBallFinset z (Cbox*3^j0) : Set (Lattice d)) :=
    le_iSup_of_le j (le_iSup_of_le hj le_rfl)
  exact hm _ (measurableSet_event_of_mem hu')

theorem finiteRangeIndependentEvents_recursivePairEvent {d R0 : ℕ} {Ω : Type*}
 [MeasurableSpace Ω] (μ : Measure Ω) (Seed : Lattice d → Set Ω)
 (R step : ℕ → ℕ) (S : ℕ → Lattice d → Finset (Lattice d))
 (hs : ∀ k x, S k x ⊆ latticeBallFinset x (step k))
 (hi : FiniteRangeIndependentEvents μ R0 Seed) (k : ℕ) :
 FiniteRangeIndependentEvents μ (2*(∑ i∈Finset.range k,step i)+R0)
   (recursivePairEvent Seed R S k)  := by
  apply finiteRangeIndependentEvents_of_local_measurable μ Seed _ hi
  intro x
  have hseed : ∀ y : Lattice d,
      MeasurableSet[eventFieldSigma Seed (latticeBallFinset y 0 : Set (Lattice d))] (Seed y) := by
    intro y
    exact measurableSet_event_of_mem (mem_latticeBallFinset_iff.mpr (by simp [latticeDist_self]))
  have hlocal := measurableSet_recursivePairEvent Seed Seed R step S hs hseed k x
  rw [Nat.zero_add] at hlocal
  exact hlocal

/-- The retained good-site field has a proved finite dependence range. -/
theorem finiteRangeIndependentEvents_truncatedBadSite {d Cdep Cbox j0 : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Lattice d → Set Ω) (hE : ∀ j z, MeasurableSet (E j z))
    (hsc : IndependentEventScales μ E)
    (hr : MultiscaleFiniteRangeIndependentEvents μ (fun j => Cdep*3^j) E) :
    FiniteRangeIndependentEvents μ ((2*Cbox+Cdep)*3^j0) (truncatedBadSite E Cbox j0)  := by
  intro S T hsep
  let r : ℕ := Cbox*3^j0
  let Splus : Set (Lattice d) := ⋃ x ∈ S, (latticeBallFinset x r : Set (Lattice d))
  let Tplus : Set (Lattice d) := ⋃ x ∈ T, (latticeBallFinset x r : Set (Lattice d))
  have hsp : ∀ j < j0+1, Indep (eventFieldSigma (E j) Splus) (eventFieldSigma (E j) Tplus) μ := by
    intro j hj
    refine hr j Splus Tplus (latticeThickening_separated ?_)
    intro x hx y hy
    have hpow : Cdep*3^j ≤ Cdep*3^j0 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hh := hsep x hx y hy
    dsimp [r]
    nlinarith
  have hi := indep_event_truncations μ E Splus Tplus (j0+1) hE hsc hsp
  have hle (U : Set (Lattice d)) :
      eventFieldSigma (truncatedBadSite E Cbox j0) U ≤
        ⨆ j ∈ Finset.range (j0+1), eventFieldSigma (E j)
          (⋃ x ∈ U, (latticeBallFinset x r : Set (Lattice d))) := by
    refine eventFieldSigma_le_of_measurable _ U _ fun x hx => ?_
    have hm : (⨆ j ∈ Finset.range (j0+1), eventFieldSigma (E j)
        (latticeBallFinset x r : Set (Lattice d))) ≤
        ⨆ j ∈ Finset.range (j0+1), eventFieldSigma (E j)
          (⋃ y ∈ U, (latticeBallFinset y r : Set (Lattice d))) :=
      iSup_mono fun j => iSup_mono fun _ =>
        eventFieldSigma_mono (E j) (latticeBallFinset_subset_thickening hx)
    exact hm _ (measurableSet_truncatedBadSite E x)
  exact indep_of_subsigmas μ hi (hle S) (hle T)

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
