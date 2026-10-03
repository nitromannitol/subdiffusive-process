module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalASDSiteFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalASDClauses

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-- A set of `ℓ^∞` diameter exceeding `R` contains a point at distance more than
`R / 2` from any of its points. -/
theorem exists_far_of_not_hasLatticeDiameterAtMost {S : Set (Lattice d)} {R : ℝ}
    (v : Lattice d) (h : ¬ HasLatticeDiameterAtMost S R) :
    ∃ c ∈ S, R < 2 * ((latticeDist v c : ℕ) : ℝ) := by
  rw [HasLatticeDiameterAtMost] at h
  push_neg at h
  obtain ⟨a, ha, b, hb, i, hab⟩ := h
  have hcast : ((|a i - b i| : ℤ) : ℝ) ≤ ((latticeDist a b : ℕ) : ℝ) := by
    have hle := coord_le_latticeDist a b i
    have h1 : (|a i - b i| : ℤ) = ((a i - b i).natAbs : ℤ) := Int.abs_eq_natAbs _
    rw [h1]
    exact_mod_cast hle
  have hab' : R < ((latticeDist a b : ℕ) : ℝ) := lt_of_lt_of_le hab hcast
  have htri : latticeDist a b ≤ latticeDist v a + latticeDist v b := by
    calc latticeDist a b ≤ latticeDist a v + latticeDist v b := latticeDist_triangle a v b
      _ = latticeDist v a + latticeDist v b := by rw [latticeDist_comm a v]
  have htriR : ((latticeDist a b : ℕ) : ℝ) ≤
      ((latticeDist v a : ℕ) : ℝ) + ((latticeDist v b : ℕ) : ℝ) := by
    exact_mod_cast htri
  rcases le_total (latticeDist v a) (latticeDist v b) with hcase | hcase
  · refine ⟨b, hb, ?_⟩
    have : ((latticeDist v a : ℕ) : ℝ) ≤ ((latticeDist v b : ℕ) : ℝ) := by exact_mod_cast hcase
    linarith
  · refine ⟨a, ha, ?_⟩
    have : ((latticeDist v b : ℕ) : ℝ) ≤ ((latticeDist v a : ℕ) : ℝ) := by exact_mod_cast hcase
    linarith

/-- **A bad component of diameter above `3 ^ (k+1)` produces an `[ASD]`
crossing.**  The bad `1`-step path witnessing the diameter is in particular a
distance-two path, and it leaves the cube `□_{k+1}(v)`. -/
theorem crossingEvent₂At_of_not_diameter
    {E : ℕ → Lattice d → Set Ω} {Cbox Cdep k : ℕ} {ω : Ω} {v : Lattice d} {R : ℝ}
    (hR : ((3 ^ (k + 1) : ℕ) : ℝ) ≤ R)
    (hdiam : ¬ HasLatticeDiameterAtMost
      (jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u} v) R) :
    ω ∈ ASD.crossingEvent₂At (asdSiteEvent E Cbox Cdep) k v := by
  classical
  obtain ⟨c, hc, hcdist⟩ := exists_far_of_not_hasLatticeDiameterAtMost v hdiam
  obtain ⟨path, hhead, hlast, hstep, hgood⟩ := hc
  have hne : path ≠ [] := by rintro rfl; simp at hhead
  have hlen : 0 < path.length := List.length_pos_of_ne_nil hne
  refine ⟨v, path.length - 1, fun i => path[i]!, ASD.self_mem_cubeAt k v, ?_, ?_, ?_, ?_⟩
  · -- the path starts at `v`
    cases path with
    | nil => exact absurd rfl hne
    | cons a t =>
      have : a = v := by simpa using hhead
      simp [this]
  · -- it is a distance-two path
    intro i hi
    have hi' : i + 1 < path.length := by omega
    exact le_trans (hstep i hi') (by norm_num)
  · -- it leaves the cube of side `3 ^ (k+1)`
    have hcend : path[path.length - 1]! = c := by
      have h2 : path.getLast? = some (path.getLast hne) := List.getLast?_eq_some_getLast hne
      have h3 : path.getLast hne = c := by
        rw [h2] at hlast
        exact (Option.some_injective _ hlast).symm ▸ rfl
      rw [getElem!_pos path (path.length - 1) (by omega), List.getLast_eq_getElem hne] at *
      exact h3
    show path[path.length - 1]! ∉ ASD.cubeAt (k + 1) v
    rw [hcend, ASD.mem_cubeAt_iff]
    intro hlt
    have hlt' : 2 * latticeDist v c < 3 ^ (k + 1) := hlt
    have hltR : ((3 ^ (k + 1) : ℕ) : ℝ) ≤ 2 * ((latticeDist v c : ℕ) : ℝ) := by
      linarith
    have hnat : (3 : ℕ) ^ (k + 1) ≤ 2 * latticeDist v c := by exact_mod_cast hltR
    omega
  · -- every site of the path is bad
    intro i hi
    have hilt : i < path.length := by omega
    rw [iUnion_asdSiteEvent]
    have hmem : path[i]! ∈ path := by
      rw [getElem!_pos path i hilt]
      exact List.getElem_mem hilt
    exact hgood _ hmem

/-- **The union bound over the centres of `B_m(z)`.**  The `[ASD]` failure event
at integer radius `m` and diameter threshold `R` is covered by the crossing
events at scale `k`, provided `3 ^ (k+1) ≤ R`. -/
theorem badComponentFailureEvent_subset_iUnion_crossing
    {E : ℕ → Lattice d → Set Ω} {Cbox Cdep k m : ℕ} {R : ℝ}
    (hR : ((3 ^ (k + 1) : ℕ) : ℝ) ≤ R) (z : Lattice d) :
    badComponentFailureEvent E Cbox 1 z (m : ℝ) R ⊆
      ⋃ v ∈ latticeBallFinset z m,
        ASD.crossingEvent₂At (asdSiteEvent E Cbox Cdep) k v := by
  rintro ω ⟨v, hv, -, hdiam⟩
  refine Set.mem_biUnion (mem_latticeBallFinset_iff.mpr ?_)
    (crossingEvent₂At_of_not_diameter hR hdiam)
  refine latticeDist_le_iff.mpr fun i => ?_
  have h : ((|v i - z i| : ℤ) : ℝ) ≤ (m : ℝ) := hv i
  rw [Int.abs_eq_natAbs] at h
  have h2 : (v i - z i).natAbs ≤ m := by exact_mod_cast h
  have hneg : (z i - v i) = -(v i - z i) := by ring
  rw [hneg, Int.natAbs_neg]
  exact h2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
