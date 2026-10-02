import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalLayeredBudget
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalBandCap




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Ω : Type*}

/-! ## Triadic band counts -/

/-- The number of geodesic indices `k ≤ n` whose radius lies in the triadic band
`[3 ^ j, 3 ^ (j+1))`. -/
def bandCount (T : ℕ → ℕ) (n j : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => 3 ^ j ≤ T k ∧ T k < 3 ^ (j + 1))).card

/-- The pointwise triadic bound, in band form: a single term is a constant plus the
contribution of its **own** band. -/
theorem pow_le_sum_band (dim : ℕ) (t J : ℕ) (ht : t < 3 ^ J) :
    (2 * t + 3) ^ dim ≤
      5 ^ dim + 9 ^ dim * ∑ j ∈ Finset.range J,
        (if 3 ^ j ≤ t ∧ t < 3 ^ (j + 1) then 3 ^ (j * dim) else 0) := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · have h1 : (2 * 0 + 3) ^ dim ≤ 5 ^ dim := Nat.pow_le_pow_left (by omega) dim
    omega
  · set m : ℕ := Nat.log 3 t with hm
    have hlow : 3 ^ m ≤ t := Nat.pow_log_le_self 3 (by omega)
    have hhigh : t < 3 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
    have hmJ : m < J := by
      by_contra hcon
      have : 3 ^ J ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hterm : 3 ^ (m * dim) ≤
        ∑ j ∈ Finset.range J, (if 3 ^ j ≤ t ∧ t < 3 ^ (j + 1) then 3 ^ (j * dim) else 0) := by
      have hmem : m ∈ Finset.range J := Finset.mem_range.mpr hmJ
      have hsingle := Finset.single_le_sum
        (f := fun j => if 3 ^ j ≤ t ∧ t < 3 ^ (j + 1) then 3 ^ (j * dim) else 0)
        (fun j _ => Nat.zero_le _) hmem
      simpa only [if_pos (⟨hlow, hhigh⟩ : 3 ^ m ≤ t ∧ t < 3 ^ (m + 1))] using hsingle
    have hbase : 2 * t + 3 ≤ 9 * 3 ^ m := by
      have h3 : (3 : ℕ) ≤ 3 ^ (m + 1) := by
        calc (3 : ℕ) = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hexp : 3 ^ (m + 1) = 3 * 3 ^ m := by rw [pow_succ]; ring
      omega
    have hpow : (2 * t + 3) ^ dim ≤ 9 ^ dim * 3 ^ (m * dim) := by
      calc (2 * t + 3) ^ dim ≤ (9 * 3 ^ m) ^ dim := Nat.pow_le_pow_left hbase dim
        _ = 9 ^ dim * (3 ^ m) ^ dim := by rw [Nat.mul_pow]
        _ = 9 ^ dim * 3 ^ (m * dim) := by rw [← pow_mul]
    have hmul : 9 ^ dim * 3 ^ (m * dim) ≤
        9 ^ dim * ∑ j ∈ Finset.range J,
          (if 3 ^ j ≤ t ∧ t < 3 ^ (j + 1) then 3 ^ (j * dim) else 0) :=
      Nat.mul_le_mul_left _ hterm
    exact le_trans (le_trans hpow hmul) (Nat.le_add_left _ _)

/-- **The band bound on the per-component length budget.** -/
theorem sum_pow_le_bandCount (dim : ℕ) (T : ℕ → ℕ) (n J : ℕ)
    (hT : ∀ k, k ≤ n → T k < 3 ^ J) :
    (∑ k ∈ Finset.range (n + 1), (2 * T k + 3) ^ dim)
      ≤ 5 ^ dim * (n + 1) +
        9 ^ dim * ∑ j ∈ Finset.range J, 3 ^ (j * dim) * bandCount T n j := by
  classical
  have hstep : (∑ k ∈ Finset.range (n + 1), (2 * T k + 3) ^ dim) ≤
      ∑ k ∈ Finset.range (n + 1),
        (5 ^ dim + 9 ^ dim *
          ∑ j ∈ Finset.range J,
            (if 3 ^ j ≤ T k ∧ T k < 3 ^ (j + 1) then 3 ^ (j * dim) else 0)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    exact pow_le_sum_band dim (T k) J (hT k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  refine hstep.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.card_range,
    ← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.range J,
      (∑ k ∈ Finset.range (n + 1),
        (if 3 ^ j ≤ T k ∧ T k < 3 ^ (j + 1) then 3 ^ (j * dim) else 0))
        = 3 ^ (j * dim) * bandCount T n j := by
    intro j _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, bandCount, mul_comm]
  rw [Finset.sum_congr rfl hinner]
  have hcomm : (n + 1) * 5 ^ dim = 5 ^ dim * (n + 1) := by ring
  omega

/-- **What the band union bound has to prove.**  Exactly the layered statement of
`Section9ChemicalLayeredBudget.geodesicTubeCost_le_of_layerCount`, with `layerCount` replaced
by `bandCount`. -/
theorem geodesicTubeCost_le_of_bandCount (v w : Lattice d) (T : ℕ → ℕ) (J M : ℕ)
    (hT : ∀ k, k ≤ latticeDist v w → T k < 3 ^ J)
    (hband : ∀ j, j < J → 3 ^ (j * (d + 1)) * bandCount T (latticeDist v w) j ≤ M) :
    2 * geodesicTubeCost d v w T ≤
      2 * (5 ^ d * (latticeDist v w + 1)) + 9 ^ d * (3 * M) := by
  classical
  set n : ℕ := latticeDist v w with hn
  have hmain := sum_pow_le_bandCount d T n J hT
  set c : ℕ → ℕ := fun j => 3 ^ (j * d) * bandCount T n j with hc
  have hcbound : ∀ j, j < J → 3 ^ j * c j ≤ M := by
    intro j hj
    have h := hband j hj
    have hexp : 3 ^ (j * (d + 1)) = 3 ^ j * 3 ^ (j * d) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hexp] at h
    calc 3 ^ j * c j = 3 ^ j * 3 ^ (j * d) * bandCount T n j := by rw [hc]; ring
      _ ≤ M := h
  have hgeom := sum_le_of_three_pow_mul_le J hcbound
  have hcost : geodesicTubeCost d v w T
      = ∑ k ∈ Finset.range (n + 1), (2 * T k + 3) ^ d := rfl
  rw [hcost]
  have hmul : 2 * (9 ^ d * ∑ j ∈ Finset.range J, c j) ≤ 9 ^ d * (3 * M) := by
    calc 2 * (9 ^ d * ∑ j ∈ Finset.range J, c j)
        = 9 ^ d * (2 * ∑ j ∈ Finset.range J, c j) := by ring
      _ ≤ 9 ^ d * (3 * M) := Nat.mul_le_mul_left _ hgeom
  calc 2 * ∑ k ∈ Finset.range (n + 1), (2 * T k + 3) ^ d
      ≤ 2 * (5 ^ d * (n + 1) + 9 ^ d * ∑ j ∈ Finset.range J, c j) :=
        Nat.mul_le_mul_left _ hmain
    _ = 2 * (5 ^ d * (n + 1)) + 2 * (9 ^ d * ∑ j ∈ Finset.range J, c j) := by ring
    _ ≤ 2 * (5 ^ d * (n + 1)) + 9 ^ d * (3 * M) := Nat.add_le_add_left hmul _

/-! ## The band events -/

/-- **The site event of a band.**  The bad `1`-step component of `x` reaches `ℓ∞` distance
`3 ^ j` and no farther than `3 ^ (j+1)`. -/
def bandSiteEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (x : Lattice d) (j : ℕ) : Set Ω :=
  {ω | (∃ y ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u} x,
          3 ^ j ≤ latticeDist x y) ∧
        ∀ y ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u} x,
          latticeDist x y ≤ 3 ^ (j + 1)}

/-- **The band-excess event.**  At least `m` sites of the `ℓ∞` geodesic from `v` to `w` carry a
bad component whose reach lies in the band `[3 ^ j, 3 ^ (j+1)]`. -/
def bandExcessEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (v w : Lattice d) (j m : ℕ) :
    Set Ω :=
  {ω | m ≤ ((Finset.range (latticeDist v w + 1)).filter
      (fun k => ω ∈ bandSiteEvent E Cbox (latticeGeodesic v w k) j)).card}

/-- The predicate of `Nat.findGreatest` holds at a nonzero value of `Nat.findGreatest`. -/
theorem findGreatest_spec_of_ne_zero {P : ℕ → Prop} [DecidablePred P] {b : ℕ}
    (h : Nat.findGreatest P b ≠ 0) : P (Nat.findGreatest P b) := by
  classical
  have hex : ∃ m, 0 < m ∧ m ≤ b ∧ P m := by
    by_contra hcon
    push_neg at hcon
    exact h (Nat.findGreatest_eq_zero_iff.mpr fun m hm hmb => hcon m hm hmb)
  obtain ⟨m, _, hmb, hPm⟩ := hex
  exact Nat.findGreatest_spec hmb hPm

/-! ## The reduction of the adaptive-tube residual -/

/-- **The band reduction of the linear budget.**

At a budget covering `5 ^ d (2 L + 1) + 9 ^ d · 3 M / 2` — linear in `L` and `M`, hence of the
frozen shape `Clen * L` once `M` is taken proportional to `L` — the adaptive-tube residual is
contained in the union of

* the **cutoff**: some site of `B_L(z)` carries a bad component of reach at least `3 ^ J`
  (`Section9ChemicalBadChain.measure_badDiameterEvent_le_exp` bounds this at a rate *linear* in
  `3 ^ J`), and
* the **band excesses**: for some pair of endpoints in `B_L(z)` and some band `j < J`, more
  than `M / 3 ^ (j (d+1))` sites of the geodesic carry a bad component of reach in that band.

The radius schedule realising the reduction is the truncated reach
`T k = findGreatest (fun t => the component at the k-th geodesic site reaches t) (3 ^ J - 1)`,
which is admissible precisely because the cutoff has been excluded. -/
theorem adaptiveTubeFailureEvent_subset_bandUnion
    (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (z : Lattice d) (L J M : ℕ) {bud : ℝ}
    (hbud : ((2 * (5 ^ d * (2 * L + 1)) + 9 ^ d * (3 * M) : ℕ) : ℝ) ≤ 2 * bud) :
    adaptiveTubeFailureEvent E Cbox z L bud ⊆
      (⋃ x ∈ latticeBallFinset z L, badDiameterEvent E Cbox x (3 ^ J)) ∪
        ⋃ v ∈ latticeBallFinset z L, ⋃ w ∈ latticeBallFinset z L, ⋃ j ∈ Finset.range J,
          bandExcessEvent E Cbox v w j (M / 3 ^ (j * (d + 1)) + 1) := by
  classical
  rintro ω ⟨v, w, hv, hw, hcost⟩
  set n : ℕ := latticeDist v w with hn
  have hzv : latticeDist z v ≤ L := latticeDist_le_of_inLatticeBallReal_natRadius hv
  have hzw : latticeDist z w ≤ L := latticeDist_le_of_inLatticeBallReal_natRadius hw
  have hvball : v ∈ latticeBallFinset z L := mem_latticeBallFinset_iff.mpr hzv
  have hwball : w ∈ latticeBallFinset z L := mem_latticeBallFinset_iff.mpr hzw
  have hgeoball : ∀ k, latticeGeodesic v w k ∈ latticeBallFinset z L := by
    intro k
    rw [mem_latticeBallFinset_iff]
    exact latticeDist_le_of_inLatticeBallReal_natRadius
      (inLatticeBallReal_latticeGeodesic hv hw k)
  by_cases hcut : ∃ k, k ≤ n ∧ ω ∈ badDiameterEvent E Cbox (latticeGeodesic v w k) (3 ^ J)
  · obtain ⟨k, -, hev⟩ := hcut
    exact Or.inl (Set.mem_biUnion (Finset.mem_coe.mpr (hgeoball k)) hev)
  refine Or.inr ?_
  push_neg at hcut
  -- the truncated reach schedule
  have hJone : 1 ≤ 3 ^ J := Nat.one_le_pow _ _ (by norm_num)
  set P : ℕ → ℕ → Prop :=
    fun k t => ω ∈ badDiameterEvent E Cbox (latticeGeodesic v w k) t with hP
  set T : ℕ → ℕ := fun k => Nat.findGreatest (P k) (3 ^ J - 1) with hT
  have hTdef : ∀ k, T k = Nat.findGreatest (P k) (3 ^ J - 1) := fun k => rfl
  have hTlt : ∀ k, T k < 3 ^ J := by
    intro k
    have h := Nat.findGreatest_le (P := P k) (3 ^ J - 1)
    rw [hTdef k]
    omega
  -- admissibility of the schedule
  have hreach : ∀ k, k ≤ n → ∀ u ∈ jStepComponent 1
      {x | ¬ IsPercolationGoodSite E Cbox ω x} (latticeGeodesic v w k),
      latticeDist (latticeGeodesic v w k) u ≤ T k := by
    intro k hk u hu
    have hlt : latticeDist (latticeGeodesic v w k) u < 3 ^ J := by
      by_contra hcon
      exact hcut k hk ⟨u, hu, Nat.le_of_not_lt hcon⟩
    rw [hTdef k]
    exact Nat.le_findGreatest (by omega) ⟨u, hu, le_rfl⟩
  have hadm : ∀ k, k ≤ n →
      ¬ IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
      ∀ u ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
          (latticeGeodesic v w k),
        latticeDist (latticeGeodesic v w k) u ≤ T k :=
    fun k hk _ u hu => hreach k hk u hu
  have hcostT := hcost T hadm
  by_cases hbands : ∀ j, j < J → 3 ^ (j * (d + 1)) * bandCount T n j ≤ M
  · -- every band is within budget, so the cost is too: contradiction
    exfalso
    have hkey := geodesicTubeCost_le_of_bandCount v w T J M (fun k _ => hTlt k) hbands
    rw [← hn] at hkey
    have hvw : n ≤ 2 * L := by
      have htri := latticeDist_triangle v z w
      rw [latticeDist_comm v z] at htri
      omega
    have hmono : 2 * (5 ^ d * (n + 1)) ≤ 2 * (5 ^ d * (2 * L + 1)) := by
      have : 5 ^ d * (n + 1) ≤ 5 ^ d * (2 * L + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hnat : 2 * geodesicTubeCost d v w T
        ≤ 2 * (5 ^ d * (2 * L + 1)) + 9 ^ d * (3 * M) := by omega
    have hrealcast : ((2 * geodesicTubeCost d v w T : ℕ) : ℝ) ≤
        ((2 * (5 ^ d * (2 * L + 1)) + 9 ^ d * (3 * M) : ℕ) : ℝ) := by exact_mod_cast hnat
    have hfinal : ((geodesicTubeCost d v w T : ℕ) : ℝ) ≤ bud := by
      have h2 : ((2 * geodesicTubeCost d v w T : ℕ) : ℝ) ≤ 2 * bud :=
        le_trans hrealcast hbud
      push_cast at h2
      linarith
    exact absurd hcostT (not_lt.mpr hfinal)
  · -- some band is over-populated
    push_neg at hbands
    obtain ⟨j, hj, hlt⟩ := hbands
    refine Set.mem_biUnion (Finset.mem_coe.mpr hvball)
      (Set.mem_biUnion (Finset.mem_coe.mpr hwball)
        (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hj)) ?_))
    have hcard : M / 3 ^ (j * (d + 1)) + 1 ≤ bandCount T n j := by
      have hpos : 0 < 3 ^ (j * (d + 1)) := by
        have := Nat.one_le_pow (j * (d + 1)) 3 (by norm_num)
        omega
      have hdiv : M / 3 ^ (j * (d + 1)) < bandCount T n j :=
        Nat.div_lt_of_lt_mul hlt
      omega
    have hsubset : ((Finset.range (n + 1)).filter
          (fun k => 3 ^ j ≤ T k ∧ T k < 3 ^ (j + 1))) ⊆
        ((Finset.range (n + 1)).filter
          (fun k => ω ∈ bandSiteEvent E Cbox (latticeGeodesic v w k) j)) := by
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      obtain ⟨hkr, hlow, hhigh⟩ := hk
      refine ⟨hkr, ?_, ?_⟩
      · have hne : T k ≠ 0 := by
          have h1 : (1 : ℕ) ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
          omega
        rw [hTdef k] at hne
        obtain ⟨y, hy, hdy⟩ := findGreatest_spec_of_ne_zero (P := P k) hne
        exact ⟨y, hy, le_trans hlow (le_trans (by rw [hTdef k]) hdy)⟩
      · intro y hy
        exact le_trans (hreach k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hkr)) y hy)
          (by omega)
    exact le_trans hcard (Finset.card_le_card hsubset)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
