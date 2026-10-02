import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalRenormalizationStep
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolationGeometry




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Finset Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The separation dichotomy -/

/-- A set of lattice sites has `ℓ^∞` diameter at most `R`, in the `ℕ`-valued
lattice metric.  This is the integer companion of
`SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.HasLatticeDiameterAtMost`. -/
def HasLatticeDistDiameterAtMost (S : Set (Lattice d)) (R : ℕ) : Prop :=
  ∀ v ∈ S, ∀ w ∈ S, latticeDist v w ≤ R

/-- The integer diameter bound implies the real one used by
`FiniteRangePercolationGeometry`. -/
theorem hasLatticeDiameterAtMost_of_hasLatticeDistDiameterAtMost
    {S : Set (Lattice d)} {R : ℕ} (h : HasLatticeDistDiameterAtMost S R) :
    HasLatticeDiameterAtMost S (R : ℝ) := by
  intro v hv w hw i
  have hnat : (v i - w i).natAbs ≤ R := (coord_le_latticeDist v w i).trans (h v hv w hw)
  have hint : (|v i - w i| : ℤ) ≤ (R : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  exact_mod_cast hint

/-- **The dichotomy.**  For a finite family `S` of sub-box centres and a sample
`ω`, either the bad centres of `S` form a single cluster of diameter at most `R`,
or two of them are separated by more than `R` — and any such pair is a member of
`separatedPairs R S`. -/
theorem exists_mem_separatedPairs_of_not_clustered
    {Bad : Lattice d → Set Ω} {R : ℕ} {S : Finset (Lattice d)} {ω : Ω}
    (h : ¬ ∀ y ∈ S, ∀ w ∈ S, ω ∈ Bad y → ω ∈ Bad w → latticeDist y w ≤ R) :
    ∃ yz ∈ separatedPairs R S, ω ∈ Bad yz.1 ∧ ω ∈ Bad yz.2 := by
  push_neg at h
  obtain ⟨y, hyS, w, hwS, hby, hbw, hd⟩ := h
  refine ⟨(y, w), ?_, hby, hbw⟩
  simp only [separatedPairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hyS, hwS⟩, hd⟩

/-! ## The forcing datum, and the inclusion -/



def ClusteredBadForcing (Bad : Lattice d → Set Ω) (Next Cross : Set Ω)
    (R : ℕ) (S : Finset (Lattice d)) : Prop :=
  ∀ ω : Ω, ω ∉ Cross →
    (∀ y ∈ S, ∀ w ∈ S, ω ∈ Bad y → ω ∈ Bad w → latticeDist y w ≤ R) →
    ω ∉ Next

/-- **The forcing inclusion.**  The DRS routing datum is exactly the hypothesis
`hdec` of `measure_le_ofReal_twoSeedStep`. -/
theorem twoSeedDecomposition_of_clusteredBadForcing
    {Bad : Lattice d → Set Ω} {Next Cross : Set Ω} {R : ℕ} {S : Finset (Lattice d)}
    (hforce : ClusteredBadForcing Bad Next Cross R S) :
    Next ⊆ (⋃ yz ∈ separatedPairs R S, Bad yz.1 ∩ Bad yz.2) ∪ Cross := by
  intro ω hω
  by_cases hc : ω ∈ Cross
  · exact Or.inr hc
  · refine Or.inl ?_
    obtain ⟨yz, hyz, hby, hbw⟩ :=
      exists_mem_separatedPairs_of_not_clustered (Bad := Bad) (R := R) (S := S)
        (ω := ω) (fun hcl => hforce ω hc hcl hω)
    exact Set.mem_biUnion hyz ⟨hby, hbw⟩

/-- **The one-step recursion, keyed on the forcing datum.**

This is `measure_le_ofReal_twoSeedStep` with its set-theoretic hypothesis
discharged by the deterministic routing of `[DRS, Theorem 3.1]`. -/
theorem measure_le_ofReal_twoSeedStep_of_clusteredBadForcing
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Bad : Lattice d → Set Ω} {Next Cross : Set Ω} {R : ℕ} {S : Finset (Lattice d)}
    {pk ek gk : ℝ} (hpk : 0 ≤ pk) (hek : 0 ≤ ek) (hgk : 0 ≤ gk)
    (hindep : FiniteRangeIndependentEvents μ R Bad)
    (hp : ∀ y, μ (Bad y) ≤ ENNReal.ofReal pk)
    (hcross : μ Cross ≤ ENNReal.ofReal gk)
    (hcard : ((separatedPairs R S).card : ℝ) ≤ Real.exp ek)
    (hforce : ClusteredBadForcing Bad Next Cross R S) :
    μ Next ≤ ENNReal.ofReal (Real.exp ek * (pk ^ 2 + gk)) :=
  measure_le_ofReal_twoSeedStep hpk hek hgk hindep hp hcross hcard
    (twoSeedDecomposition_of_clusteredBadForcing hforce)

/-! ## The detour is bounded independently of the level -/

/-- A chain of level-`k` sub-box centres whose `ℓ^∞` displacement grows at least
linearly in the index gap.  A straight axis chain of sub-boxes of side `L_k`,
which is what the DRS construction follows across a level-`(k+1)` box, satisfies
this with `step = L_k`. -/
def IsQuasiGeodesicChain (step : ℕ) (y : ℕ → Lattice d) : Prop :=
  ∀ i j : ℕ, i ≤ j → step * (j - i) ≤ latticeDist (y i) (y j)

/-- **The detour window.**  Along a quasi-geodesic chain, two bad centres are at
index gap at most `R / step`.  With the level-`k` dependence radius `R < L_k` and
the spacing `step = L_k`, the gap is `0`: the cluster meets the chain in a single
index. -/
theorem badIndex_window_of_quasiGeodesic {step R : ℕ} {y : ℕ → Lattice d}
    (hstep : 0 < step) (hchain : IsQuasiGeodesicChain step y)
    {Badset : Set (Lattice d)}
    (hcluster : ∀ u ∈ Badset, ∀ v ∈ Badset, latticeDist u v ≤ R)
    {i j : ℕ} (hij : i ≤ j) (hi : y i ∈ Badset) (hj : y j ∈ Badset) :
    j - i ≤ R / step := by
  have hmul : step * (j - i) ≤ R := (hchain i j hij).trans (hcluster _ hi _ hj)
  rw [Nat.mul_comm] at hmul
  exact (Nat.le_div_iff_mul_le hstep).mpr hmul

/-- With `R < step` the window degenerates: a quasi-geodesic chain meets the bad
cluster in at most one index. -/
theorem badIndex_unique_of_quasiGeodesic {step R : ℕ} {y : ℕ → Lattice d}
    (hstep : 0 < step) (hRstep : R < step) (hchain : IsQuasiGeodesicChain step y)
    {Badset : Set (Lattice d)}
    (hcluster : ∀ u ∈ Badset, ∀ v ∈ Badset, latticeDist u v ≤ R)
    {i j : ℕ} (hi : y i ∈ Badset) (hj : y j ∈ Badset) : i = j := by
  have hdiv : R / step = 0 := Nat.div_eq_of_lt hRstep
  rcases le_total i j with h | h
  · have hw := badIndex_window_of_quasiGeodesic hstep hchain hcluster h hi hj
    rw [hdiv, Nat.le_zero] at hw
    omega
  · have hw := badIndex_window_of_quasiGeodesic hstep hchain hcluster h hj hi
    rw [hdiv, Nat.le_zero] at hw
    omega

/-- **The detour count.**  The bad indices of a quasi-geodesic chain of length `N`
number at most `R / step + 1`, uniformly in `N`.  This is the additive level
overhead `C` of `Section9ChemicalWaypointChain`. -/
theorem card_badIndices_le_of_quasiGeodesic {step R N : ℕ} {y : ℕ → Lattice d}
    (hstep : 0 < step) (hchain : IsQuasiGeodesicChain step y)
    {Badset : Set (Lattice d)} [DecidablePred fun i => y i ∈ Badset]
    (hcluster : ∀ u ∈ Badset, ∀ v ∈ Badset, latticeDist u v ≤ R) :
    ((Finset.range N).filter fun i => y i ∈ Badset).card ≤ R / step + 1 := by
  classical
  set T := (Finset.range N).filter fun i => y i ∈ Badset with hT
  rcases Finset.eq_empty_or_nonempty T with hempty | hne
  · simp [hempty]
  obtain ⟨m, hm, hmle⟩ := T.exists_min_image id hne
  have hmBad : y m ∈ Badset := (Finset.mem_filter.mp hm).2
  set W := R / step with hW
  have hsub : T ⊆ Finset.Icc m (m + W) := by
    intro i hi
    have hiBad : y i ∈ Badset := (Finset.mem_filter.mp hi).2
    have hmi : m ≤ i := hmle i hi
    have hwin := badIndex_window_of_quasiGeodesic hstep hchain hcluster hmi hmBad hiBad
    exact Finset.mem_Icc.mpr ⟨hmi, by omega⟩
  calc T.card ≤ (Finset.Icc m (m + W)).card := Finset.card_le_card hsub
    _ = W + 1 := by rw [Nat.card_Icc, Nat.add_assoc, Nat.add_sub_cancel_left]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
