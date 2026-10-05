module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingCrossingPerCellFailure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionCrossingScaleCap

@[expose] public section

/-!
# The deterministic content of a short repaired crossing: telescoping,
# scale splitting, and the failure charge

This module isolates, in its **correct** shape, the deterministic half of the
manuscript's multiscale crossing lemma
A short repaired-graph crossing of
the bracket `k` is turned into a *weighted family of failed triadic cubes*:

* §1 a short crossing supplies an adjacency chain `cells 0, …, cells N` with
  `N < ⌈epsilon 3 ^ k⌉`, starting in the source family and ending on a cell
  that meets the exterior of `B(x0, 3 ^ k R)`;
* §2 the step bound telescopes along the chain;
* §3 hence `∑ i ≤ N, 3 ^ (scale (cells i)) ≥ (3 ^ k R - R) / 107`;
* §4 cells of scale below `base + J` cannot carry that sum once
  `epsilon ≤ 3 ^ (-J) / 424` and `J + 5 ≤ k`, so the cells of scale at least
  `base + J` carry at least `3 ^ (k + base) / 150`;
* §5 each such cell charges, by the one-sided per-cell law, to a failed cube of
  scale at least `base + J - 1`, giving a family of failed cubes of cardinality
  at most `⌈epsilon 3 ^ k⌉` with `∑ 3 ^ (scale) ≥ 3 ^ (k + base) / 450`.

## What this replaces

One might instead try to conclude a *connected chain of failure balls*, with consecutive centres within
`92 max (3 ^ f_i) (3 ^ f_{i+1})`.  That shape is **false**: nothing prevents a
long run of base-scale cells between two consecutive cells of scale at least
`base + J`, and such a run can move the path a distance
`≈ 105 · 3 ^ base · epsilon 3 ^ k ≈ 3 ^ (k + base - J) / 4`, which exceeds
`92 · 3 ^ (base + J)` by the unbounded factor `3 ^ (k - 2 J)`.  The link bound
is therefore not available, and the union bound over chains that it was meant
to feed is refuted by this scale comparison.  What *is* true is the weighted family
below, and it is the deterministic input of the manuscript's own induction.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-! ## 0. The crossing width attached to a scale threshold -/

/-- **The crossing width attached to a scale threshold.**  The deterministic
step below fixes the *shape* of the admissible crossing width: a threshold `J`
on the cell scale forces `epsilon ≤ 3 ^ (-J) / 424`.  Once the
probabilistic step names a dimensional threshold `J = J d`, the exterior row's
crossing width is `repairedStoppingCrossingWidth (J d)`, a quantity depending
on the dimension alone — which is the scope the frozen v3 exterior row
requires, since its decay constant `c ≤ epsilon * log 2 / 3` is chosen before
the model, the source and the radius. -/
def repairedStoppingCrossingWidth (J : ℕ) : ℝ := (3 : ℝ) ^ (-(J : ℤ)) / 424

omit [NeZero d] in
theorem repairedStoppingCrossingWidth_pos (J : ℕ) :
    0 < repairedStoppingCrossingWidth J := by
  rw [repairedStoppingCrossingWidth]
  positivity

/-! ## 1. The adjacency chain of a short crossing -/

/-- **A short crossing is an adjacency chain.**  A shortest walk from the
source family to the exterior cell has fewer than `⌈epsilon 3 ^ k⌉` edges, so
its vertex sequence is an adjacency chain of that length beginning in the
source and ending on a cell that meets the exterior of the bracket ball. -/
theorem exists_adjChain_of_repairedStoppingShortCrossing
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (x0 : Vec d) (R epsilon : ℝ) (k : ℕ)
    (hcross : RepairedStoppingShortCrossing source hsource x0 R epsilon k) :
    ∃ (N : ℕ) (cells : ℕ → RefinedStoppingCell failure omega base),
      N < ⌈epsilon * (3 : ℝ) ^ k⌉₊ ∧ cells 0 ∈ source ∧
      (translatedCube d (refinedStoppingScale (cells N))
          (refinedStoppingCenter (cells N)) ∩
        (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty ∧
      ∀ i, i < N → repairedStoppingGraph.Adj (cells i) (cells (i + 1)) := by
  obtain ⟨q, hqmeet, hqdist⟩ := hcross
  obtain ⟨s, hs, hqs⟩ :=
    exists_source_dist_eq_stoppingGraphDistance repairedStoppingGraph hsource q
  have hconnected := repairedStoppingGraph_connected failure omega hinitial hrepair
  obtain ⟨forward, hforward⟩ := hconnected.exists_walk_length_eq_dist q s
  set walk := forward.reverse with hwalk
  have hlength : walk.length =
      stoppingGraphDistance repairedStoppingGraph source hsource q := by
    simp only [hwalk, SimpleGraph.Walk.length_reverse, hforward, hqs]
  refine ⟨walk.length, walk.getVert, hlength ▸ hqdist, ?_, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.getVert_zero] using hs
  · simpa only [SimpleGraph.Walk.getVert_length] using hqmeet
  · intro i hi
    exact walk.adj_getVert_succ hi

/-! ## 2. Telescoping the step bound -/

/-- **The telescoped step bound.**  Along an adjacency chain the refined centre
moves by at most `105` times the side length of the *arriving* cell at each
step. -/
theorem dist_refinedStoppingCenter_le_sum_of_adjChain
    {cells : ℕ → RefinedStoppingCell failure omega base} {N : ℕ}
    (hadj : ∀ i, i < N → repairedStoppingGraph.Adj (cells i) (cells (i + 1))) :
    dist (refinedStoppingCenter (cells 0)) (refinedStoppingCenter (cells N)) ≤
      ∑ i ∈ Finset.range N,
        105 * (3 : ℝ) ^ refinedStoppingScale (cells (i + 1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hstep : dist (refinedStoppingCenter (cells n))
        (refinedStoppingCenter (cells (n + 1))) ≤
        105 * (3 : ℝ) ^ refinedStoppingScale (cells (n + 1)) :=
      dist_refinedStoppingCenter_le_of_repairedStoppingGraph_adj
        (hadj n (by omega))
    have hrec := ih fun i hi ↦ hadj i (by omega)
    have htri := dist_triangle (refinedStoppingCenter (cells 0))
      (refinedStoppingCenter (cells n)) (refinedStoppingCenter (cells (n + 1)))
    rw [Finset.sum_range_succ]
    linarith

/-- **A source cell is near the source ball.**  Its centred threefold
enlargement meets `closedBall x0 R`, so its centre is within `R + 3/2` side
lengths of `x0`. -/
theorem dist_refinedStoppingCenter_le_of_mem_repairedStoppingSourceCells
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) {R : ℝ} {q : RefinedStoppingCell failure omega base}
    (hq : q ∈ repairedStoppingSourceCells hinitial hrepair x0 R) :
    dist (refinedStoppingCenter q) x0 ≤
      R + 3 / 2 * (3 : ℝ) ^ refinedStoppingScale q := by
  obtain ⟨z, hzcell, hzball⟩ :=
    (mem_repairedStoppingSourceCells_iff hinitial hrepair x0 R q).mp hq
  have hz := dist_refinedStoppingCenter_lt_of_mem_enlargement hzcell
  have hzR : dist z x0 ≤ R := Metric.mem_closedBall.mp hzball
  have htri : dist (refinedStoppingCenter q) x0 ≤
      dist (refinedStoppingCenter q) z + dist z x0 := dist_triangle _ _ _
  have hsf : cubeScaleFactor (refinedStoppingFailureCube q) =
      (3 : ℝ) ^ refinedStoppingScale q := rfl
  rw [hsf] at hz
  linarith

/-- **Unconditional localization along the chain.**  Without any scale cap, the
`i`-th cell of a chain issued from the source family lies within
`R + 3/2 · (side of the first cell) + 105 · (the partial side-length sum)` of
`x0`.  This is the tube in which the failed cubes charged in §5 live; a *ball*
localization needs a scale cap and is supplied by
`dist_refinedStoppingCenter_le_of_stoppingGraphDistance_le`. -/
theorem dist_refinedStoppingCenter_le_of_adjChain
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) {R : ℝ} {i : ℕ}
    {cells : ℕ → RefinedStoppingCell failure omega base}
    (hzero : cells 0 ∈ repairedStoppingSourceCells hinitial hrepair x0 R)
    (hadj : ∀ j, j < i → repairedStoppingGraph.Adj (cells j) (cells (j + 1))) :
    dist (refinedStoppingCenter (cells i)) x0 ≤
      R + 3 / 2 * (3 : ℝ) ^ refinedStoppingScale (cells 0) +
        ∑ j ∈ Finset.range i,
          105 * (3 : ℝ) ^ refinedStoppingScale (cells (j + 1)) := by
  have hstart := dist_refinedStoppingCenter_le_of_mem_repairedStoppingSourceCells
    hinitial hrepair x0 hzero
  have htel := dist_refinedStoppingCenter_le_sum_of_adjChain hadj
  have htri : dist (refinedStoppingCenter (cells i)) x0 ≤
      dist (refinedStoppingCenter (cells i)) (refinedStoppingCenter (cells 0)) +
        dist (refinedStoppingCenter (cells 0)) x0 := dist_triangle _ _ _
  rw [dist_comm (refinedStoppingCenter (cells i))
    (refinedStoppingCenter (cells 0))] at htri
  linarith

/-! ## 3. The total side-length sum of a short crossing -/

/-- **A short crossing needs side length.**  The chain of a crossing to the
bracket radius `3 ^ k R` from the source family at radius `R` has total cell
side length at least `(3 ^ k R - R) / 107`. -/
theorem sum_pow_refinedStoppingScale_ge_of_adjChain
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) {R : ℝ} {k N : ℕ}
    {cells : ℕ → RefinedStoppingCell failure omega base}
    (hzero : cells 0 ∈ repairedStoppingSourceCells hinitial hrepair x0 R)
    (hmeet : (translatedCube d (refinedStoppingScale (cells N))
        (refinedStoppingCenter (cells N)) ∩
      (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty)
    (hadj : ∀ i, i < N → repairedStoppingGraph.Adj (cells i) (cells (i + 1))) :
    (3 : ℝ) ^ k * R - R ≤
      107 * ∑ i ∈ Finset.range (N + 1),
        (3 : ℝ) ^ refinedStoppingScale (cells i) := by
  classical
  set s : ℕ → ℝ := fun i ↦ (3 : ℝ) ^ refinedStoppingScale (cells i) with hs
  have hspos : ∀ i, 0 < s i := fun i ↦ zpow_pos (by norm_num) _
  set T : ℝ := ∑ i ∈ Finset.range (N + 1), s i with hT
  have hs0T : s 0 ≤ T :=
    Finset.single_le_sum (f := s) (fun i _ ↦ (hspos i).le)
      (Finset.mem_range.mpr (by omega))
  have hsNT : s N ≤ T :=
    Finset.single_le_sum (f := s) (fun i _ ↦ (hspos i).le)
      (Finset.mem_range.mpr (by omega))
  -- the source endpoint
  have hstart : dist (refinedStoppingCenter (cells 0)) x0 ≤ R + 3 / 2 * s 0 :=
    dist_refinedStoppingCenter_le_of_mem_repairedStoppingSourceCells hinitial
      hrepair x0 hzero
  -- the exterior endpoint
  have hend : (3 : ℝ) ^ k * R - 1 / 2 * s N ≤
      dist (refinedStoppingCenter (cells N)) x0 := by
    obtain ⟨z, hzcell, hzball⟩ := hmeet
    rw [translatedCube_eq_metricBall, Metric.mem_ball] at hzcell
    have hzout : (3 : ℝ) ^ k * R ≤ dist z x0 := by
      have := hzball
      rw [mem_compl_iff, Metric.mem_ball, not_lt] at this
      exact this
    have htri : dist z x0 ≤
        dist z (refinedStoppingCenter (cells N)) +
          dist (refinedStoppingCenter (cells N)) x0 := dist_triangle _ _ _
    have hzc : dist z (refinedStoppingCenter (cells N)) < 1 / 2 * s N := by
      simpa only [hs] using hzcell
    linarith
  have htel := dist_refinedStoppingCenter_le_sum_of_adjChain hadj
  have hsum : ∑ i ∈ Finset.range N, 105 * s (i + 1) = 105 * (T - s 0) := by
    have hshift : ∑ i ∈ Finset.range N, s (i + 1) = T - s 0 := by
      rw [hT, Finset.sum_range_succ']
      ring
    rw [← Finset.mul_sum, hshift]
  have htri : dist (refinedStoppingCenter (cells N)) x0 ≤
      dist (refinedStoppingCenter (cells N)) (refinedStoppingCenter (cells 0)) +
        dist (refinedStoppingCenter (cells 0)) x0 := dist_triangle _ _ _
  rw [dist_comm (refinedStoppingCenter (cells N))
    (refinedStoppingCenter (cells 0))] at htri
  rw [hsum] at htel
  have hs0 := hspos 0
  have hsN := hspos N
  linarith

/-! ## 4. Splitting off the small cells -/

/-- The bookkeeping inequality behind the scale split: with `X = 3 ^ k`,
`B = 3 ^ base`, `Y = 3 ^ J`, a total side length `T` at least `(B X - B)/107`
and a small-cell contribution `SB` at most `M · B Y / 3` with
`M ≤ epsilon X + 1` and `epsilon ≤ 1 / (424 Y)`, at least `X B / 150` of the
side length sits on the cells of scale at least `base + J`. -/
private theorem splitting_arith {X B Y M T SB eps : ℝ}
    (hX : (243 : ℝ) ≤ X) (hB : 0 < B) (hY : 1 ≤ Y)
    (hYX : 243 * Y ≤ X) (hMle : M ≤ eps * X + 1)
    (heps : eps ≤ 1 / (424 * Y))
    (hSB : SB ≤ M * (B * Y / 3))
    (hT : B * X - B ≤ 107 * T) :
    X * B / 150 ≤ T - SB := by
  have hXpos : (0 : ℝ) < X := by linarith
  have hYpos : (0 : ℝ) < Y := by linarith
  have hBX : B ≤ X * B / 243 := by nlinarith [hX, hB]
  have hTlow : X * B * 242 / (243 * 107) ≤ T := by nlinarith [hT, hBX, hB]
  have h424 : eps * (424 * Y) ≤ 1 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 424 * Y)] at heps
    linarith
  have hXB : (0 : ℝ) < X * B := by positivity
  have h2 : eps * X * (B * Y / 3) ≤ X * B / 1272 := by
    nlinarith [mul_le_mul_of_nonneg_right h424 (le_of_lt hXB), hXB]
  have hBY3 : (0 : ℝ) ≤ B * Y / 3 := by positivity
  have h3 : M * (B * Y / 3) ≤ X * B / 1272 + B * Y / 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hMle hBY3, h2]
  have h4 : B * Y / 3 ≤ X * B / 729 := by nlinarith [hYX, hB]
  linarith

/-- **The scale split.**  Once the crossing width satisfies
`epsilon ≤ 3 ^ (-J) / 424` and the bracket exceeds the threshold by five, the
cells of scale below `base + J` cannot carry the side length a short crossing
needs: the cells of scale at least `base + J` carry at least
`3 ^ (k + base) / 150`. -/
theorem sum_large_pow_refinedStoppingScale_ge_of_adjChain
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) {R epsilon : ℝ} {J k N : ℕ}
    {cells : ℕ → RefinedStoppingCell failure omega base}
    (hbase : (3 : ℝ) ^ base ≤ R) (hJk : J + 5 ≤ k)
    (heps : epsilon ≤ repairedStoppingCrossingWidth J)
    (hN : N < ⌈epsilon * (3 : ℝ) ^ k⌉₊)
    (hzero : cells 0 ∈ repairedStoppingSourceCells hinitial hrepair x0 R)
    (hmeet : (translatedCube d (refinedStoppingScale (cells N))
        (refinedStoppingCenter (cells N)) ∩
      (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty)
    (hadj : ∀ i, i < N → repairedStoppingGraph.Adj (cells i) (cells (i + 1))) :
    (3 : ℝ) ^ k * (3 : ℝ) ^ base / 150 ≤
      ∑ i ∈ (Finset.range (N + 1)).filter
          (fun i ↦ base + (J : ℤ) ≤ refinedStoppingScale (cells i)),
        (3 : ℝ) ^ refinedStoppingScale (cells i) := by
  classical
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  set s : ℕ → ℝ := fun i ↦ (3 : ℝ) ^ refinedStoppingScale (cells i) with hs
  have hspos : ∀ i, 0 < s i := fun i ↦ zpow_pos (by norm_num) _
  set X : ℝ := (3 : ℝ) ^ k with hX
  set B : ℝ := (3 : ℝ) ^ base with hB
  set Y : ℝ := (3 : ℝ) ^ (J : ℤ) with hY
  have hBpos : (0 : ℝ) < B := zpow_pos (by norm_num) _
  have hYone : (1 : ℝ) ≤ Y := one_le_zpow₀ (by norm_num) (by positivity)
  have hX243 : (243 : ℝ) ≤ X := by
    have h5 : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h5
    simpa [hX] using h5
  have hYX : 243 * Y ≤ X := by
    have hcast : Y = (3 : ℝ) ^ J := by rw [hY, zpow_natCast]
    have : (3 : ℝ) ^ (J + 5) ≤ (3 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) hJk
    rw [pow_add] at this
    rw [hcast, hX]
    nlinarith [this]
  -- the total side length
  have hTotal : B * X - B ≤ 107 * ∑ i ∈ Finset.range (N + 1), s i := by
    have hstep := sum_pow_refinedStoppingScale_ge_of_adjChain hinitial hrepair
      x0 hzero hmeet hadj
    have hXone : (1 : ℝ) ≤ X := by linarith
    have hRB : B ≤ R := hbase
    nlinarith [hstep, hXone, hRB]
  -- the small cells
  set A : Finset ℕ := (Finset.range (N + 1)).filter
    (fun i ↦ base + (J : ℤ) ≤ refinedStoppingScale (cells i)) with hA
  set Ac : Finset ℕ := (Finset.range (N + 1)).filter
    (fun i ↦ ¬ base + (J : ℤ) ≤ refinedStoppingScale (cells i)) with hAc
  have hpartition : ∑ i ∈ A, s i + ∑ i ∈ Ac, s i =
      ∑ i ∈ Finset.range (N + 1), s i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsmallval : (3 : ℝ) ^ (base + (J : ℤ) - 1) = B * Y / 3 := by
    rw [hB, hY, show base + (J : ℤ) - 1 = base + ((J : ℤ) + (-1)) by ring,
      zpow_add₀ h3ne, zpow_add₀ h3ne]
    norm_num
    ring
  have hsmall : ∀ i ∈ Ac, s i ≤ B * Y / 3 := by
    intro i hi
    rw [hAc, Finset.mem_filter] at hi
    have hle : refinedStoppingScale (cells i) ≤ base + (J : ℤ) - 1 := by omega
    rw [← hsmallval]
    exact zpow_le_zpow_right₀ (by norm_num) hle
  have hcard : (Ac.card : ℝ) ≤ epsilon * X + 1 := by
    have h1 : Ac.card ≤ N + 1 := by
      calc Ac.card ≤ (Finset.range (N + 1)).card := Finset.card_filter_le _ _
        _ = N + 1 := Finset.card_range _
    have hpos : 0 < ⌈epsilon * X⌉₊ := by omega
    have hepspos : 0 < epsilon * X := Nat.ceil_pos.mp hpos
    have hlt : (⌈epsilon * X⌉₊ : ℝ) < epsilon * X + 1 :=
      Nat.ceil_lt_add_one hepspos.le
    have h2 : ((N : ℝ) + 1) ≤ (⌈epsilon * X⌉₊ : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hN
    have h3 : (Ac.card : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hSB : ∑ i ∈ Ac, s i ≤ (Ac.card : ℝ) * (B * Y / 3) := by
    calc ∑ i ∈ Ac, s i ≤ ∑ _i ∈ Ac, B * Y / 3 :=
          Finset.sum_le_sum hsmall
      _ = (Ac.card : ℝ) * (B * Y / 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hepsY : epsilon ≤ 1 / (424 * Y) := by
    have hYpos : (0 : ℝ) < Y := by linarith
    have hinv : (3 : ℝ) ^ (-(J : ℤ)) = 1 / Y := by
      rw [hY, zpow_neg, one_div]
    rw [repairedStoppingCrossingWidth, hinv] at heps
    rw [div_div] at heps
    calc epsilon ≤ 1 / (Y * 424) := heps
      _ = 1 / (424 * Y) := by ring_nf
  have hmain := splitting_arith (X := X) (B := B) (Y := Y)
    (M := (Ac.card : ℝ)) (T := ∑ i ∈ Finset.range (N + 1), s i)
    (SB := ∑ i ∈ Ac, s i) (eps := epsilon) hX243 hBpos hYone hYX hcard hepsY
    hSB hTotal
  have : X * B / 150 ≤ ∑ i ∈ A, s i := by linarith [hpartition, hmain]
  simpa only [hX, hB, hs, hA] using this

/-! ## 5. The weighted family of failed cubes -/

/-- **The deterministic datum of a short crossing.**  A short crossing at
bracket `k` and width `epsilon ≤ 3 ^ (-J) / 424`, with `J + 5 ≤ k`, produces a
family of at most `epsilon 3 ^ k + 1` failed triadic cubes, each of scale at
least `base + J - 1`, whose side lengths sum to at least
`3 ^ (k + base) / 450`.

This is the corrected form of the deterministic step; see the module docstring
for why the connected-chain form is unavailable.  The *localization* of the
family inside the bracket ball is not part of this statement: it is supplied,
under a scale cap, by `dist_refinedStoppingCenter_le_of_stoppingGraphDistance_le`
together with the `45 · 3 ^ scale` charge distance of
`exists_failure_at_one_sided_offset_refinedStoppingCell`. -/
theorem exists_failureFamily_of_repairedStoppingShortCrossing
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) {R epsilon : ℝ} {J k : ℕ}
    (hbase : (3 : ℝ) ^ base ≤ R) (hJ : 1 ≤ J) (hJk : J + 5 ≤ k)
    (heps : epsilon ≤ repairedStoppingCrossingWidth J)
    (hcross : RepairedStoppingShortCrossing
      (repairedStoppingSourceCells hinitial hrepair x0 R)
      (repairedStoppingSourceCells_nonempty hinitial hrepair x0
        (le_trans (zpow_pos (by norm_num) base).le hbase)) x0 R epsilon k) :
    ∃ (A : Finset ℕ) (F : ℕ → TriadicCube d),
      (A.card : ℝ) ≤ epsilon * (3 : ℝ) ^ k + 1 ∧
      (∀ i ∈ A, omega ∈ failure (F i)) ∧
      (∀ i ∈ A, base + (J : ℤ) - 1 ≤ (F i).scale) ∧
      (3 : ℝ) ^ k * (3 : ℝ) ^ base / 450 ≤ ∑ i ∈ A, (3 : ℝ) ^ (F i).scale := by
  classical
  have : Nonempty (TriadicCube d) := ⟨⟨0, fun _ ↦ 0⟩⟩
  obtain ⟨N, cells, hN, hzero, hmeet, hadj⟩ :=
    exists_adjChain_of_repairedStoppingShortCrossing hinitial hrepair _ _ x0 R
      epsilon k hcross
  set A : Finset ℕ := (Finset.range (N + 1)).filter
    (fun i ↦ base + (J : ℤ) ≤ refinedStoppingScale (cells i)) with hA
  have hlarge := sum_large_pow_refinedStoppingScale_ge_of_adjChain hinitial
    hrepair x0 hbase hJk heps hN hzero hmeet hadj
  have hbaselt : ∀ i ∈ A, base < refinedStoppingScale (cells i) := by
    intro i hi
    rw [hA, Finset.mem_filter] at hi
    omega
  choose! r F hr hFscale hFfail hFdist using
    fun i (hi : i ∈ A) ↦ exists_failure_at_one_sided_offset_refinedStoppingCell
      hfinite (cells i) (hbaselt i hi)
  refine ⟨A, F, ?_, fun i hi ↦ hFfail i hi, ?_, ?_⟩
  · have h1 : A.card ≤ N + 1 := by
      calc A.card ≤ (Finset.range (N + 1)).card := Finset.card_filter_le _ _
        _ = N + 1 := Finset.card_range _
    have hpos : 0 < ⌈epsilon * (3 : ℝ) ^ k⌉₊ := by omega
    have hepspos : 0 < epsilon * (3 : ℝ) ^ k := Nat.ceil_pos.mp hpos
    have hlt : (⌈epsilon * (3 : ℝ) ^ k⌉₊ : ℝ) < epsilon * (3 : ℝ) ^ k + 1 :=
      Nat.ceil_lt_add_one hepspos.le
    have h2 : ((N : ℝ) + 1) ≤ (⌈epsilon * (3 : ℝ) ^ k⌉₊ : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hN
    have h3 : (A.card : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast h1
    linarith
  · intro i hi
    have hsc := hFscale i hi
    have hlow : base + (J : ℤ) ≤ refinedStoppingScale (cells i) := by
      rw [hA, Finset.mem_filter] at hi
      exact hi.2
    have := hr i hi
    omega
  · have hterm : ∀ i ∈ A,
        (3 : ℝ) ^ refinedStoppingScale (cells i) / 3 ≤ (3 : ℝ) ^ (F i).scale := by
      intro i hi
      have hsc := hFscale i hi
      have hrge := hr i hi
      have hle : refinedStoppingScale (cells i) - 1 ≤ (F i).scale := by omega
      have hmono : (3 : ℝ) ^ (refinedStoppingScale (cells i) - 1) ≤
          (3 : ℝ) ^ (F i).scale := zpow_le_zpow_right₀ (by norm_num) hle
      have hval : (3 : ℝ) ^ (refinedStoppingScale (cells i) - 1) =
          (3 : ℝ) ^ refinedStoppingScale (cells i) / 3 := by
        rw [show refinedStoppingScale (cells i) - 1 =
          refinedStoppingScale (cells i) + (-1) by ring,
          zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
        ring
      linarith [hval ▸ hmono]
    have hsum : (∑ i ∈ A, (3 : ℝ) ^ refinedStoppingScale (cells i)) / 3 ≤
        ∑ i ∈ A, (3 : ℝ) ^ (F i).scale := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum hterm
    linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
