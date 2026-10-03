module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalAdaptiveTube

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ}

/-! ## The triadic layer counts -/

/-- The number of geodesic indices `k ≤ n` at which the radius schedule reaches `3 ^ j`. -/
def layerCount (T : ℕ → ℕ) (n j : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => 3 ^ j ≤ T k)).card

theorem layerCount_antitone (T : ℕ → ℕ) (n : ℕ) {j j' : ℕ} (h : j ≤ j') :
    layerCount T n j' ≤ layerCount T n j := by
  refine Finset.card_le_card ?_
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, le_trans (Nat.pow_le_pow_right (by norm_num) h) hk.2⟩

/-- The pointwise triadic bound: a single term is a constant plus the layers below it. -/
theorem pow_le_sum_layer (dim : ℕ) (t J : ℕ) (ht : t < 3 ^ J) :
    (2 * t + 3) ^ dim ≤
      5 ^ dim + 9 ^ dim * ∑ j ∈ Finset.range J, (if 3 ^ j ≤ t then 3 ^ (j * dim) else 0) := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · have h1 : (2 * 0 + 3) ^ dim ≤ 5 ^ dim := Nat.pow_le_pow_left (by omega) dim
    omega
  · set m : ℕ := Nat.log 3 t with hm
    have hlow : 3 ^ m ≤ t := Nat.pow_log_le_self 3 (by omega)
    have hmJ : m < J := by
      by_contra hcon
      have : 3 ^ J ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hhigh : t < 3 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
    have hterm : 3 ^ (m * dim) ≤
        ∑ j ∈ Finset.range J, (if 3 ^ j ≤ t then 3 ^ (j * dim) else 0) := by
      have hmem : m ∈ Finset.range J := Finset.mem_range.mpr hmJ
      have hsingle := Finset.single_le_sum
        (f := fun j => if 3 ^ j ≤ t then 3 ^ (j * dim) else 0)
        (fun j _ => Nat.zero_le _) hmem
      simpa only [if_pos hlow] using hsingle
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
        9 ^ dim * ∑ j ∈ Finset.range J, (if 3 ^ j ≤ t then 3 ^ (j * dim) else 0) :=
      Nat.mul_le_mul_left _ hterm
    exact le_trans (le_trans hpow hmul) (Nat.le_add_left _ _)

/-- **The layered bound on the per-component length budget.** -/
theorem sum_pow_le_layerCount (dim : ℕ) (T : ℕ → ℕ) (n J : ℕ)
    (hT : ∀ k, k ≤ n → T k < 3 ^ J) :
    (∑ k ∈ Finset.range (n + 1), (2 * T k + 3) ^ dim)
      ≤ 5 ^ dim * (n + 1) +
        9 ^ dim * ∑ j ∈ Finset.range J, 3 ^ (j * dim) * layerCount T n j := by
  classical
  have hstep : (∑ k ∈ Finset.range (n + 1), (2 * T k + 3) ^ dim) ≤
      ∑ k ∈ Finset.range (n + 1),
        (5 ^ dim + 9 ^ dim *
          ∑ j ∈ Finset.range J, (if 3 ^ j ≤ T k then 3 ^ (j * dim) else 0)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    exact pow_le_sum_layer dim (T k) J
      (hT k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  refine hstep.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.card_range,
    ← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.range J,
      (∑ k ∈ Finset.range (n + 1), (if 3 ^ j ≤ T k then 3 ^ (j * dim) else 0))
        = 3 ^ (j * dim) * layerCount T n j := by
    intro j _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, layerCount, mul_comm]
  rw [Finset.sum_congr rfl hinner]
  have hcomm : (n + 1) * 5 ^ dim = 5 ^ dim * (n + 1) := by ring
  omega

/-! ## The geometric series -/

/-- If every layer obeys `3 ^ j · c j ≤ M`, the layers sum to at most `3 M / 2`. -/
theorem sum_le_of_three_pow_mul_le {c : ℕ → ℕ} {M : ℕ} :
    ∀ J : ℕ, (∀ j, j < J → 3 ^ j * c j ≤ M) →
      2 * ∑ j ∈ Finset.range J, c j ≤ 3 * M := by
  have key : ∀ J : ℕ, (∀ j, j < J → 3 ^ j * c j ≤ M) →
      2 * 3 ^ J * (∑ j ∈ Finset.range J, c j) ≤ 3 * M * (3 ^ J - 1) := by
    intro J
    induction J with
    | zero => intro _; simp
    | succ J ih =>
      intro h
      have hIH := ih fun j hj => h j (by omega)
      have hJ := h J (by omega)
      have hp : (1 : ℕ) ≤ 3 ^ J := Nat.one_le_pow _ _ (by norm_num)
      have hexp : 3 ^ (J + 1) = 3 * 3 ^ J := by rw [pow_succ]; ring
      rw [Finset.sum_range_succ]
      have hgoal : 2 * 3 ^ (J + 1) * (∑ j ∈ Finset.range J, c j + c J)
          = 3 * (2 * 3 ^ J * ∑ j ∈ Finset.range J, c j) + 6 * (3 ^ J * c J) := by
        rw [hexp]; ring
      rw [hgoal]
      have h1 : 3 * (2 * 3 ^ J * ∑ j ∈ Finset.range J, c j) ≤ 3 * (3 * M * (3 ^ J - 1)) :=
        Nat.mul_le_mul_left _ hIH
      have h2 : 6 * (3 ^ J * c J) ≤ 6 * M := Nat.mul_le_mul_left _ hJ
      have h3 : 3 * (3 * M * (3 ^ J - 1)) + 6 * M ≤ 3 * M * (3 ^ (J + 1) - 1) := by
        rw [hexp]
        have hexpand : 3 * M * (3 * 3 ^ J - 1) = 9 * M * (3 ^ J - 1) + 6 * M := by
          have h9 : 3 * 3 ^ J - 1 = 3 * (3 ^ J - 1) + 2 := by omega
          rw [h9]; ring
        rw [hexpand]
        have hre : 3 * (3 * M * (3 ^ J - 1)) = 9 * M * (3 ^ J - 1) := by ring
        omega
      omega
  intro J h
  have hkey := key J h
  have hp : (1 : ℕ) ≤ 3 ^ J := Nat.one_le_pow _ _ (by norm_num)
  have hle : 2 * 3 ^ J * (∑ j ∈ Finset.range J, c j) ≤ 3 * M * 3 ^ J := by
    refine hkey.trans ?_
    exact Nat.mul_le_mul_left _ (by omega)
  have hpos : 0 < 3 ^ J := by positivity
  have hrw : 2 * 3 ^ J * (∑ j ∈ Finset.range J, c j)
      = (2 * ∑ j ∈ Finset.range J, c j) * 3 ^ J := by ring
  have hrw2 : 3 * M * 3 ^ J = (3 * M) * 3 ^ J := by ring
  rw [hrw, hrw2] at hle
  exact Nat.le_of_mul_le_mul_right hle hpos

/-! ## The sufficient per-layer condition -/

/-- **What the layered union bound has to prove.**

If the radius schedule is bounded by `3 ^ J` along the geodesic and every triadic layer obeys
`3 ^ (j (d+1)) · N_j ≤ M`, then twice the per-component length budget is at most
`2 · 5 ^ d (n+1) + 9 ^ d · 3 M`, i.e. **linear** in `n` and `M`.

Taking `M = ε L` with `n = latticeDist v w ≤ 2 L` makes the right-hand side `Clen · L` with
`Clen` a constant fixed before `L`, which is exactly what clause (iii) of the frozen anchor
demands. -/
theorem geodesicTubeCost_le_of_layerCount (v w : Lattice d) (T : ℕ → ℕ) (J M : ℕ)
    (hT : ∀ k, k ≤ latticeDist v w → T k < 3 ^ J)
    (hlayer : ∀ j, j < J → 3 ^ (j * (d + 1)) * layerCount T (latticeDist v w) j ≤ M) :
    2 * geodesicTubeCost d v w T ≤
      2 * (5 ^ d * (latticeDist v w + 1)) + 9 ^ d * (3 * M) := by
  classical
  set n : ℕ := latticeDist v w with hn
  have hmain := sum_pow_le_layerCount d T n J hT
  set c : ℕ → ℕ := fun j => 3 ^ (j * d) * layerCount T n j with hc
  have hcbound : ∀ j, j < J → 3 ^ j * c j ≤ M := by
    intro j hj
    have h := hlayer j hj
    have hexp : 3 ^ (j * (d + 1)) = 3 ^ j * 3 ^ (j * d) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hexp] at h
    calc 3 ^ j * c j = 3 ^ j * 3 ^ (j * d) * layerCount T n j := by rw [hc]; ring
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


/-! ## The entropy absorption of the layered union bound

The union bound over `m`-tuples of separated chains rooted on the geodesic pays, per root, the
entropy `log (e n / m)` of choosing the roots plus the level entropy `j · d · log 3` of the
chain, against the gain `β q 3 ^ j` of a layer-`j` chain.  Because the entropy is *linear* in
the layer index while the gain is *exponential* in it, one threshold on `q` absorbs every
layer at once — this is the arithmetic that fails for the site-Peierls accounting
(`Section9ChemicalScaleDecision.exists_level_separated_gain_lt`) and succeeds here, because the
geodesic is one-dimensional: separating roots along it costs `3 ^ j`, not `3 ^ (j d)`. -/

theorem one_add_le_three_pow (j : ℕ) : (1 : ℝ) + (j : ℝ) ≤ (3 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ n ih =>
      have hp : (0 : ℝ) ≤ (3 : ℝ) ^ n := by positivity
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      rw [pow_succ]
      push_cast
      nlinarith

/-- The linear entropy of a layer is dominated by the layer's exponential gain, uniformly in
the layer, as soon as the rate exceeds `a + b`. -/
theorem linear_le_mul_three_pow {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b ≤ t)
    (j : ℕ) : a * (j : ℝ) + b ≤ t * (3 : ℝ) ^ j := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hlin : a * (j : ℝ) + b ≤ (a + b) * (1 + (j : ℝ)) := by nlinarith
  have hpow := one_add_le_three_pow j
  have hab : (0 : ℝ) ≤ a + b := by linarith
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ j := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hab]

/-- The root entropy of the union bound: `Nat.choose n m ≤ (n + 1) ^ m`. -/
theorem choose_le_pow_succ (n m : ℕ) : ((n.choose m : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ m := by
  have h1 : n.choose m ≤ n ^ m := Nat.choose_le_pow n m
  have h2 : n ^ m ≤ (n + 1) ^ m := Nat.pow_le_pow_left (Nat.le_succ n) m
  have h3 : n.choose m ≤ (n + 1) ^ m := le_trans h1 h2
  have h4 := (Nat.cast_le (α := ℝ)).mpr h3
  push_cast at h4
  exact h4

/-- `log t ≤ k · t ^ (1/k)`: the bounded ratio that makes the root entropy `m log (e n / m)`
lose to a gain which is a fixed power of `n / m`. -/
theorem log_le_mul_rpow {k : ℝ} (hk : 1 ≤ k) {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ≤ k * t ^ (1 / k) := by
  have hk' : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hrpowpos : (0 : ℝ) < t ^ (1 / k) := Real.rpow_pos_of_pos htpos _
  have h1 : Real.log (t ^ (1 / k)) = (1 / k) * Real.log t := Real.log_rpow htpos _
  have h2 : Real.log (t ^ (1 / k)) ≤ t ^ (1 / k) - 1 :=
    Real.log_le_sub_one_of_pos hrpowpos
  have h3 : (1 / k) * Real.log t ≤ t ^ (1 / k) := by rw [← h1]; linarith
  have h4 : k * ((1 / k) * Real.log t) ≤ k * t ^ (1 / k) :=
    mul_le_mul_of_nonneg_left h3 hk'.le
  have h5 : k * ((1 / k) * Real.log t) = Real.log t := by field_simp
  linarith

/-! ## The exact residual of the frozen linear clause -/

section Residual

variable {Ω : Type*}

open MeasureTheory Set

/-- **The layer-counting failure event.**

For the two endpoints witnessing the chemical-distance failure, *every* admissible radius
schedule along the geodesic either exceeds the cutoff `3 ^ J` at some geodesic site, or
overshoots the per-layer budget `M` at some triadic layer below `J`.

This is the exact residual of the **linear** clause (iii) of the frozen anchor, in the same
sense in which `Section9ChemicalTube.chemicalDistanceFailureEvent_subset_union_of_diameter`
was the residual of the uniform-tube route — except that it is *reachable*: the cutoff term is
a single bad-component diameter tail (`Section9ChemicalBadChain.measure_badDiameterEvent_le_exp`,
rate `exp (-c q 3 ^ J)`), and the layer terms are counting events over `m`-tuples of chains
rooted on the geodesic, whose joint weight is bounded by
`Section9ChemicalChainFamily.tsum_chainFamily_le_prod`. -/
def layerCountFailureEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (z : Lattice d) (L J M : ℕ) : Set Ω :=
  {ω | ∃ v w : Lattice d,
      InLatticeBallReal z v (L : ℝ) ∧ InLatticeBallReal z w (L : ℝ) ∧
      ∀ T : ℕ → ℕ,
        (∀ k, k ≤ latticeDist v w →
          ¬ IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
          ∀ u ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w k),
            latticeDist (latticeGeodesic v w k) u ≤ T k) →
        ((∃ k, k ≤ latticeDist v w ∧ 3 ^ J ≤ T k) ∨
          ∃ j, j < J ∧ M < 3 ^ (j * (d + 1)) * layerCount T (latticeDist v w) j)}

/-- **The layered reduction of the linear budget.**

At a budget covering `5 ^ d (2 L + 1) + 9 ^ d · 3 M / 2`, the adaptive-tube residual is
contained in the layer-counting failure event.  Since that expression is linear in `L` and
`M`, taking `M = ε L` produces a budget `Clen · L` with `Clen` fixed before `L` — the frozen
shape. -/
theorem adaptiveTubeFailureEvent_subset_layerCountFailure
    (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (z : Lattice d) (L J M : ℕ) {bud : ℝ}
    (hbud : ((2 * (5 ^ d * (2 * L + 1)) + 9 ^ d * (3 * M) : ℕ) : ℝ) ≤ 2 * bud) :
    adaptiveTubeFailureEvent E Cbox z L bud ⊆ layerCountFailureEvent E Cbox z L J M := by
  rintro ω ⟨v, w, hv, hw, hcost⟩
  refine ⟨v, w, hv, hw, fun T hT => ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hcut, hlayer⟩ := hcon
  have hcut' : ∀ k, k ≤ latticeDist v w → T k < 3 ^ J := by
    intro k hk
    exact Nat.lt_of_not_ge fun h => absurd h (by simpa using hcut k hk)
  have hlayer' : ∀ j, j < J →
      3 ^ (j * (d + 1)) * layerCount T (latticeDist v w) j ≤ M := by
    intro j hj
    exact Nat.le_of_not_lt fun h => absurd h (by simpa using hlayer j hj)
  have hkey := geodesicTubeCost_le_of_layerCount v w T J M hcut' hlayer'
  have hzv : latticeDist z v ≤ L := latticeDist_le_of_inLatticeBallReal_natRadius hv
  have hzw : latticeDist z w ≤ L := latticeDist_le_of_inLatticeBallReal_natRadius hw
  have hvw : latticeDist v w ≤ 2 * L := by
    have htri := latticeDist_triangle v z w
    rw [latticeDist_comm v z] at htri
    omega
  have hmono : 2 * (5 ^ d * (latticeDist v w + 1)) ≤ 2 * (5 ^ d * (2 * L + 1)) := by
    have : 5 ^ d * (latticeDist v w + 1) ≤ 5 ^ d * (2 * L + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hnat : 2 * geodesicTubeCost d v w T
      ≤ 2 * (5 ^ d * (2 * L + 1)) + 9 ^ d * (3 * M) := by omega
  have hreal : ((2 * geodesicTubeCost d v w T : ℕ) : ℝ) ≤
      ((2 * (5 ^ d * (2 * L + 1)) + 9 ^ d * (3 * M) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hfinal : ((geodesicTubeCost d v w T : ℕ) : ℝ) ≤ bud := by
    have h2 : ((2 * geodesicTubeCost d v w T : ℕ) : ℝ) ≤ 2 * bud := le_trans hreal hbud
    push_cast at h2
    linarith
  exact absurd (hcost T hT) (not_lt.mpr hfinal)

end Residual

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
