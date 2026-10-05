module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingCells

@[expose] public section

/-!
# The weight sum over crossing certificates

A crossing certificate is a chain of cells in which consecutive cells are within
reach of each other (`cellReach`), and in which at most `gb` cells are good
vertices.  This file bounds the total weight of all such chains starting at a
given cell:

`chainSum n gb c ≤ 2 (rad c + 1)^d (4 κ)^gb` ,

uniformly in the length bound `n`, where `κ = 2^d (J+1)^d` is the branching
constant of one step and the only hypothesis is that the *scale sum*

`π = ∑_j ((Cbox+Cdep) 3^j + 1)^{2d} · (weight of a scale-j cell)`

is small — which holds as soon as `q` is large, since the weight carries
`exp(-c q 3^{3j/2})`.

The good-vertex budget `gb` is what the crossing estimate pays for: it is the
number of good vertices allowed on the crossing path, and it enters the bound
only through the harmless factor `(4κ)^gb`, which the exponential gain
`e^{-c q l}` absorbs once the density constant `c` is small.

## Source

`mfd:in-deterministic` and `s.tightness`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## Chains -/

/-- Two cells are within reach when their centres are no farther apart than the
sum of their radii plus one `J`-step. -/
def cellReach (Cbox Cdep J : ℕ) (c c' : CrossCell d) : Prop :=
  latticeDist (cellCenter Cdep c) (cellCenter Cdep c') ≤
    cellRadius Cbox Cdep c + cellRadius Cbox Cdep c' + J

/-- The number of good-vertex cells of a chain. -/
def goodCellCount (L : List (CrossCell d)) : ℕ :=
  (L.filter (fun c => c.isRight)).length

theorem goodCellCount_nil : goodCellCount ([] : List (CrossCell d)) = 0 := rfl

theorem goodCellCount_cons (c : CrossCell d) (L : List (CrossCell d)) :
    goodCellCount (c :: L) = goodCellCount L + (if c.isRight then 1 else 0) := by
  unfold goodCellCount
  rw [List.filter_cons]
  by_cases h : c.isRight = true <;> simp [h]

/-- A chain is admissible from `c` when its consecutive cells are within reach,
its first cell is within reach of `c`, and it uses at most `gb` good vertices. -/
def AdmissibleChain (Cbox Cdep J : ℕ) (n gb : ℕ) (c : CrossCell d)
    (L : List (CrossCell d)) : Prop :=
  L.length ≤ n ∧ L.IsChain (cellReach Cbox Cdep J) ∧
    (∀ c' ∈ L.head?, cellReach Cbox Cdep J c c') ∧ goodCellCount L ≤ gb

/-- The total weight of all admissible chains of length at most `n` starting
from `c`. -/
def chainSum (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ) (n gb : ℕ) (c : CrossCell d) :
    ℝ≥0∞ :=
  ∑' L : List (CrossCell d),
    if AdmissibleChain Cbox Cdep J n gb c L then
      (L.map (cellWeight d Cdep Cprob cprob q)).prod else 0

/-! ## The two counting bounds -/

/-- The equivalence used to peel the head off a list. -/
def listHeadEquiv (α : Type*) : List α ≃ Unit ⊕ (α × List α) where
  toFun l := match l with
    | [] => Sum.inl ()
    | a :: t => Sum.inr (a, t)
  invFun x := match x with
    | Sum.inl _ => []
    | Sum.inr p => p.1 :: p.2
  left_inv l := by cases l <;> rfl
  right_inv x := by
    rcases x with u | p
    · cases u; rfl
    · rfl

theorem tsum_list_eq {α : Type*} [Countable α] (f : List α → ℝ≥0∞) :
    ∑' L : List α, f L = f [] + ∑' p : α × List α, f (p.1 :: p.2) := by
  rw [← (listHeadEquiv α).symm.tsum_eq f,
    Summable.tsum_sum ENNReal.summable ENNReal.summable]
  congr 1
  exact tsum_eq_single () fun u hu => absurd (Subsingleton.elim u ()) hu

/-- Counting the grid indices, or vertices, that a single step can reach. -/
theorem tsum_ite_ball_le (X : Lattice d) (D : ℕ) (k : ℝ≥0∞)
    (f : Lattice d → Lattice d) (hf : Function.Injective f) :
    (∑' a : Lattice d, if latticeDist X (f a) ≤ D then k else 0) ≤
      (((2 * D + 1) ^ d : ℕ) : ℝ≥0∞) * k := by
  classical
  set S : Finset (Lattice d) := (latticeBallFinset X D).preimage f hf.injOn with hS
  have hmem : ∀ a, a ∈ S ↔ latticeDist X (f a) ≤ D := by
    intro a
    rw [hS, Finset.mem_preimage, mem_latticeBallFinset_iff]
  have hzero : ∀ a ∉ S, (if latticeDist X (f a) ≤ D then k else 0) = 0 := by
    intro a ha
    rw [ite_eq_right (fun h => ha ((hmem a).mpr h))]
  rw [tsum_eq_sum hzero]
  have hsum : (∑ a ∈ S, if latticeDist X (f a) ≤ D then k else 0) = (S.card : ℝ≥0∞) * k := by
    rw [Finset.sum_congr rfl (fun a ha => ite_eq_left ((hmem a).mp ha)), Finset.sum_const,
      nsmul_eq_mul]
  rw [hsum]
  have hcard : S.card ≤ ((2 * D + 1) ^ d : ℕ) := by
    have hsub : S.card ≤ (latticeBallFinset X D).card :=
      Finset.card_le_card_of_injOn f
        (fun a ha => mem_latticeBallFinset_iff.mpr ((hmem a).mp ha)) hf.injOn
    simpa [card_latticeBallFinset] using hsub
  exact mul_le_mul' (by exact_mod_cast hcard) le_rfl

/-! ## Peeling the head of a chain -/

theorem chainSum_succ_le (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ) (n gb : ℕ)
    (c : CrossCell d) :
    chainSum Cbox Cdep J Cprob cprob q (n + 1) gb c ≤
      1 + ∑' c' : CrossCell d,
        (if cellReach Cbox Cdep J c c' ∧ (c'.isRight = true → 1 ≤ gb) then
          cellWeight d Cdep Cprob cprob q c' *
            chainSum Cbox Cdep J Cprob cprob q n
              (gb - (if c'.isRight = true then 1 else 0)) c'
        else 0) := by
  classical
  set w : CrossCell d → ℝ≥0∞ := cellWeight d Cdep Cprob cprob q with hw
  set f : List (CrossCell d) → ℝ≥0∞ := fun L =>
    if AdmissibleChain Cbox Cdep J (n + 1) gb c L then (L.map w).prod else 0 with hf
  have hnil : f [] = 1 := by
    rw [hf]
    refine (ite_eq_left ?_).trans (by simp)
    exact ⟨by simp, List.isChain_nil, by simp, by simp [goodCellCount_nil]⟩
  have hcons : ∀ c' : CrossCell d,
      (∑' L' : List (CrossCell d), f (c' :: L')) =
        (if cellReach Cbox Cdep J c c' ∧ (c'.isRight = true → 1 ≤ gb) then
          w c' * chainSum Cbox Cdep J Cprob cprob q n
            (gb - (if c'.isRight = true then 1 else 0)) c'
        else 0) := by
    intro c'
    set delta : ℕ := if c'.isRight = true then 1 else 0 with hdelta
    have hadm : ∀ L' : List (CrossCell d),
        AdmissibleChain Cbox Cdep J (n + 1) gb c (c' :: L') ↔
          (cellReach Cbox Cdep J c c' ∧ delta ≤ gb) ∧
            AdmissibleChain Cbox Cdep J n (gb - delta) c' L' := by
      intro L'
      unfold AdmissibleChain
      rw [List.isChain_cons, goodCellCount_cons, ← hdelta]
      constructor
      · rintro ⟨hlen, ⟨hhead, hch⟩, hfst, hgc⟩
        refine ⟨⟨hfst c' (by simp), by omega⟩, ⟨by simpa using hlen, hch, hhead, by omega⟩⟩
      · rintro ⟨⟨hR, hd⟩, hlen, hch, hhead, hgc⟩
        refine ⟨by simpa using hlen, ⟨hhead, hch⟩, ?_, by omega⟩
        intro y hy
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        exact hy ▸ hR
    by_cases hcond : cellReach Cbox Cdep J c c' ∧ delta ≤ gb
    · have hterm : ∀ L' : List (CrossCell d), f (c' :: L') =
          w c' * (if AdmissibleChain Cbox Cdep J n (gb - delta) c' L' then
            (L'.map w).prod else 0) := by
        intro L'
        rw [hf]
        simp only [hadm L', hcond, true_and, List.map_cons, List.prod_cons]
        by_cases h : AdmissibleChain Cbox Cdep J n (gb - delta) c' L' <;> simp [h]
      rw [tsum_congr hterm, ENNReal.tsum_mul_left]
      have hsimp : cellReach Cbox Cdep J c c' ∧ (c'.isRight = true → 1 ≤ gb) := by
        refine ⟨hcond.1, fun h => ?_⟩
        have : delta = 1 := by rw [hdelta, ite_eq_left h]
        omega
      rw [ite_eq_left hsimp, chainSum]
    · have hterm : ∀ L' : List (CrossCell d), f (c' :: L') = 0 := by
        intro L'
        have hno : ¬ AdmissibleChain Cbox Cdep J (n + 1) gb c (c' :: L') := by
          rw [hadm L']; tauto
        simp only [hf, hno, ite_false]
      have hneg : ¬ (cellReach Cbox Cdep J c c' ∧ (c'.isRight = true → 1 ≤ gb)) := by
        intro hpos
        refine hcond ⟨hpos.1, ?_⟩
        by_cases h : c'.isRight = true
        · have hgb := hpos.2 h
          have hd1 : delta = 1 := by rw [hdelta, ite_eq_left h]
          omega
        · have hd0 : delta = 0 := by rw [hdelta, ite_eq_right h]
          omega
      rw [tsum_congr hterm, ite_eq_right hneg, tsum_zero]
  calc chainSum Cbox Cdep J Cprob cprob q (n + 1) gb c
      = ∑' L : List (CrossCell d), f L := rfl
    _ = f [] + ∑' p : CrossCell d × List (CrossCell d), f (p.1 :: p.2) :=
        tsum_list_eq f
    _ = 1 + ∑' c' : CrossCell d, ∑' L' : List (CrossCell d), f (c' :: L') := by
        rw [hnil, ENNReal.tsum_prod' (f := fun p : CrossCell d × List (CrossCell d) =>
          f (p.1 :: p.2))]
    _ ≤ 1 + ∑' c' : CrossCell d,
          (if cellReach Cbox Cdep J c c' ∧ (c'.isRight = true → 1 ≤ gb) then
            w c' * chainSum Cbox Cdep J Cprob cprob q n
              (gb - (if c'.isRight = true then 1 else 0)) c'
          else 0) := by
        exact le_of_eq (by rw [tsum_congr hcons])

/-! ## The constants -/

/-- The branching constant of one chain step. -/
def crossBranch (dim J : ℕ) : ℝ≥0∞ := ((2 ^ dim * (J + 1) ^ dim : ℕ) : ℝ≥0∞)

theorem one_le_crossBranch (dim J : ℕ) : 1 ≤ crossBranch dim J := by
  rw [crossBranch]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)

theorem crossBranch_ne_top (dim J : ℕ) : crossBranch dim J ≠ ⊤ := by
  rw [crossBranch]; exact ENNReal.natCast_ne_top _

/-- The scale sum: the total weight of one step's scale choices, with the
entropy of the reachable grid points already included. -/
def crossScaleSum (dim Cbox Cdep : ℕ) (Cprob cprob q : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, ((((Cbox + Cdep) * 3 ^ j + 1) ^ (2 * dim) : ℕ) : ℝ≥0∞) *
    cellWeight dim Cdep Cprob cprob q (Sum.inl (j, (0 : Lattice dim)))

/-! ## The elementary counting inequalities -/

theorem crossBranch_count_good (dim J x : ℕ) :
    (2 * (x + 0 + J) + 1) ^ dim ≤ 2 ^ dim * (J + 1) ^ dim * (x + 1) ^ dim := by
  have hbase : 2 * (x + 0 + J) + 1 ≤ 2 * (J + 1) * (x + 1) := by
    have hexp : 2 * (J + 1) * (x + 1) = 2 * (J * x) + 2 * J + 2 * x + 2 := by ring
    rw [hexp]
    generalize J * x = t
    omega
  calc (2 * (x + 0 + J) + 1) ^ dim ≤ (2 * (J + 1) * (x + 1)) ^ dim :=
        Nat.pow_le_pow_left hbase dim
    _ = 2 ^ dim * (J + 1) ^ dim * (x + 1) ^ dim := by
        rw [mul_pow, mul_pow]

theorem crossBranch_count_event (dim J x y : ℕ) :
    (2 * (x + y + J) + 1) ^ dim ≤
      2 ^ dim * (J + 1) ^ dim * (x + 1) ^ dim * (y + 1) ^ dim := by
  have hbase : 2 * (x + y + J) + 1 ≤ 2 * (J + 1) * (x + 1) * (y + 1) := by
    have hexp : 2 * (J + 1) * (x + 1) * (y + 1) =
        2 * (J * x * y) + 2 * (J * x) + 2 * (J * y) + 2 * J + 2 * (x * y) +
          2 * x + 2 * y + 2 := by ring
    rw [hexp]
    generalize J * x * y = t1
    generalize J * x = t2
    generalize J * y = t3
    generalize x * y = t4
    omega
  calc (2 * (x + y + J) + 1) ^ dim ≤ (2 * (J + 1) * (x + 1) * (y + 1)) ^ dim :=
        Nat.pow_le_pow_left hbase dim
    _ = 2 ^ dim * (J + 1) ^ dim * (x + 1) ^ dim * (y + 1) ^ dim := by
        rw [mul_pow, mul_pow, mul_pow]

theorem crossGrid_injective (Cdep j : ℕ) :
    Function.Injective (crossGrid (d := d) Cdep j) := by
  intro a b hab
  funext i
  have h := congrFun hab i
  simp only [crossGrid] at h
  have hm : (crossMesh Cdep j : ℤ) ≠ 0 := by
    have hpos := crossMesh_pos Cdep j
    omega
  exact mul_left_cancel₀ hm h

/-! ## The two per-step sums -/

/-- The good-vertex branch of one chain step. -/
theorem tsum_good_step_le (Cbox Cdep J : ℕ) (c : CrossCell d) (k : ℝ≥0∞) :
    (∑' v : Lattice d, if cellReach Cbox Cdep J c (Sum.inr v) then k else 0) ≤
      crossBranch d J * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) * k := by
  have hcongr : ∀ v : Lattice d,
      (if cellReach Cbox Cdep J c (Sum.inr v) then k else 0) =
        (if latticeDist (cellCenter Cdep c) (id v) ≤
          cellRadius Cbox Cdep c + 0 + J then k else 0) := by
    intro v
    refine if_congr ?_ rfl rfl
    simp only [cellReach, cellCenter, cellRadius, id]
  rw [tsum_congr hcongr]
  refine (tsum_ite_ball_le (cellCenter Cdep c) (cellRadius Cbox Cdep c + 0 + J) k id
    Function.injective_id).trans ?_
  refine mul_le_mul' ?_ le_rfl
  rw [crossBranch]
  exact_mod_cast crossBranch_count_good d J (cellRadius Cbox Cdep c)

/-- The event branch of one chain step. -/
theorem tsum_event_step_le (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ) (c : CrossCell d)
    (K : ℝ≥0∞) :
    (∑' p : ℕ × Lattice d,
      (if cellReach Cbox Cdep J c (Sum.inl p) then
        cellWeight d Cdep Cprob cprob q (Sum.inl p) *
          (K * (((cellRadius Cbox Cdep (Sum.inl p) + 1) ^ d : ℕ) : ℝ≥0∞))
      else 0)) ≤
      crossBranch d J * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) * K *
        crossScaleSum d Cbox Cdep Cprob cprob q := by
  classical
  have hinner : ∀ j : ℕ,
      (∑' a : Lattice d,
        (if cellReach Cbox Cdep J c (Sum.inl (j, a)) then
          cellWeight d Cdep Cprob cprob q (Sum.inl (j, a)) *
            (K * (((cellRadius Cbox Cdep (Sum.inl (j, a)) + 1) ^ d : ℕ) : ℝ≥0∞))
        else 0)) ≤
      crossBranch d J * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) * K *
        (((((Cbox + Cdep) * 3 ^ j + 1) ^ (2 * d) : ℕ) : ℝ≥0∞) *
          cellWeight d Cdep Cprob cprob q (Sum.inl (j, (0 : Lattice d)))) := by
    intro j
    set rho : ℕ := (Cbox + Cdep) * 3 ^ j with hrho
    set wj : ℝ≥0∞ := cellWeight d Cdep Cprob cprob q (Sum.inl (j, (0 : Lattice d)))
      with hwj
    set W : ℝ≥0∞ := wj * (K * (((rho + 1) ^ d : ℕ) : ℝ≥0∞)) with hW
    have hcongr : ∀ a : Lattice d,
        (if cellReach Cbox Cdep J c (Sum.inl (j, a)) then
          cellWeight d Cdep Cprob cprob q (Sum.inl (j, a)) *
            (K * (((cellRadius Cbox Cdep (Sum.inl (j, a)) + 1) ^ d : ℕ) : ℝ≥0∞))
        else 0) =
        (if latticeDist (cellCenter Cdep c) (crossGrid Cdep j a) ≤
          cellRadius Cbox Cdep c + rho + J then W else 0) := by
      intro a
      refine if_congr ?_ ?_ rfl
      · simp only [cellReach, cellCenter, cellRadius, hrho]
      · rw [hW, hwj]
        rfl
    rw [tsum_congr hcongr]
    refine (tsum_ite_ball_le (cellCenter Cdep c) (cellRadius Cbox Cdep c + rho + J) W
      (crossGrid Cdep j) (crossGrid_injective Cdep j)).trans ?_
    have hcount : (((2 * (cellRadius Cbox Cdep c + rho + J) + 1) ^ d : ℕ) : ℝ≥0∞) ≤
        crossBranch d J * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) *
          (((rho + 1) ^ d : ℕ) : ℝ≥0∞) := by
      rw [crossBranch]
      exact_mod_cast crossBranch_count_event d J (cellRadius Cbox Cdep c) rho
    have hsq : ((((rho + 1) ^ d : ℕ) : ℝ≥0∞)) * ((((rho + 1) ^ d : ℕ) : ℝ≥0∞)) =
        (((rho + 1) ^ (2 * d) : ℕ) : ℝ≥0∞) := by
      rw [← Nat.cast_mul, ← pow_add]
      congr 2
      ring
    calc (((2 * (cellRadius Cbox Cdep c + rho + J) + 1) ^ d : ℕ) : ℝ≥0∞) * W
        ≤ (crossBranch d J * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) *
            (((rho + 1) ^ d : ℕ) : ℝ≥0∞)) * W := mul_le_mul' hcount le_rfl
      _ = crossBranch d J * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) * K *
            (((((rho + 1) ^ d : ℕ) : ℝ≥0∞) * (((rho + 1) ^ d : ℕ) : ℝ≥0∞)) * wj) := by
          rw [hW]; ring
      _ = crossBranch d J * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) * K *
            ((((rho + 1) ^ (2 * d) : ℕ) : ℝ≥0∞) * wj) := by rw [hsq]
  calc (∑' p : ℕ × Lattice d,
        (if cellReach Cbox Cdep J c (Sum.inl p) then
          cellWeight d Cdep Cprob cprob q (Sum.inl p) *
            (K * (((cellRadius Cbox Cdep (Sum.inl p) + 1) ^ d : ℕ) : ℝ≥0∞))
        else 0))
      = ∑' (j : ℕ) (a : Lattice d),
          (if cellReach Cbox Cdep J c (Sum.inl (j, a)) then
            cellWeight d Cdep Cprob cprob q (Sum.inl (j, a)) *
              (K * (((cellRadius Cbox Cdep (Sum.inl (j, a)) + 1) ^ d : ℕ) : ℝ≥0∞))
          else 0) := ENNReal.tsum_prod'
    _ ≤ ∑' j : ℕ, crossBranch d J *
          (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) * K *
          (((((Cbox + Cdep) * 3 ^ j + 1) ^ (2 * d) : ℕ) : ℝ≥0∞) *
            cellWeight d Cdep Cprob cprob q (Sum.inl (j, (0 : Lattice d)))) :=
        ENNReal.tsum_le_tsum hinner
    _ = crossBranch d J * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) * K *
          crossScaleSum d Cbox Cdep Cprob cprob q := by
        rw [ENNReal.tsum_mul_left, crossScaleSum]


/-! ## The uniform bound on the chain sum -/

/-- **The total weight of all crossing certificates from one cell.**

Uniform in the length bound: the only cost of the chain's length is the good
budget `gb`, and the scale sum `π` being small is exactly what makes the
geometric series converge. -/
theorem chainSum_le (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ)
    (hpi : 8 * crossBranch d J * crossBranch d J *
      crossScaleSum d Cbox Cdep Cprob cprob q ≤ 2 * crossBranch d J) :
    ∀ (n gb : ℕ) (c : CrossCell d),
      chainSum Cbox Cdep J Cprob cprob q n gb c ≤
        2 * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) *
          (4 * crossBranch d J) ^ gb := by
  classical
  set kappa : ℝ≥0∞ := crossBranch d J with hkappa
  set pival : ℝ≥0∞ := crossScaleSum d Cbox Cdep Cprob cprob q with hpival
  have hk1 : 1 ≤ kappa := one_le_crossBranch d J
  have hktop : kappa ≠ ⊤ := crossBranch_ne_top d J
  have hAle : (1 : ℝ≥0∞) ≤ 4 * kappa := le_trans hk1 (by
    calc kappa = 1 * kappa := (one_mul _).symm
      _ ≤ 4 * kappa := by gcongr; norm_num)
  have hXone : ∀ c : CrossCell d,
      (1 : ℝ≥0∞) ≤ (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) := by
    intro c
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- the scale sum is small enough
  have hsmall : 2 * kappa * pival ≤ 1 := by
    have h4ne : (4 * kappa) ≠ 0 := by
      refine mul_ne_zero (by norm_num) ?_
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hk1)
    have h4top : (4 * kappa) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hktop
    have hstep : 4 * kappa * (2 * kappa * pival) ≤ 4 * kappa * 1 := by
      calc 4 * kappa * (2 * kappa * pival) = 8 * kappa * kappa * pival := by ring
        _ ≤ 2 * kappa := hpi
        _ ≤ 4 * kappa * 1 := by rw [mul_one]; gcongr; norm_num
    exact (ENNReal.mul_le_mul_iff_right h4ne h4top).mp hstep
  intro n
  induction n with
  | zero =>
      intro gb c
      have hzero : ∀ L : List (CrossCell d), L ≠ [] →
          (if AdmissibleChain Cbox Cdep J 0 gb c L then
            (L.map (cellWeight d Cdep Cprob cprob q)).prod else 0) = 0 := by
        intro L hL
        rw [ite_eq_right]
        rintro ⟨hlen, -⟩
        exact hL (List.eq_nil_of_length_eq_zero (by omega))
      have hval : chainSum Cbox Cdep J Cprob cprob q 0 gb c ≤ 1 := by
        rw [chainSum, tsum_eq_single [] hzero]
        by_cases h : AdmissibleChain Cbox Cdep J 0 gb c ([] : List (CrossCell d)) <;>
          simp [h]
      refine hval.trans ?_
      calc (1 : ℝ≥0∞) ≤ (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) := hXone c
        _ ≤ 2 * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) *
              (4 * kappa) ^ gb := by
            calc (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞)
                = 1 * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) * 1 := by ring
              _ ≤ 2 * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) *
                    (4 * kappa) ^ gb := by
                  gcongr
                  · norm_num
                  · exact one_le_pow₀ hAle
  | succ n ih =>
      intro gb c
      set X : ℝ≥0∞ := (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) with hX
      set A : ℝ≥0∞ := 4 * kappa with hA
      refine (chainSum_succ_le Cbox Cdep J Cprob cprob q n gb c).trans ?_
      -- replace the inner chain sums by the inductive bound
      have hstep : ∀ c' : CrossCell d,
          (if cellReach Cbox Cdep J c c' ∧ (c'.isRight = true → 1 ≤ gb) then
            cellWeight d Cdep Cprob cprob q c' *
              chainSum Cbox Cdep J Cprob cprob q n
                (gb - (if c'.isRight = true then 1 else 0)) c'
          else 0) ≤
          (if cellReach Cbox Cdep J c c' ∧ (c'.isRight = true → 1 ≤ gb) then
            cellWeight d Cdep Cprob cprob q c' *
              (2 * (((cellRadius Cbox Cdep c' + 1) ^ d : ℕ) : ℝ≥0∞) *
                A ^ (gb - (if c'.isRight = true then 1 else 0)))
          else 0) := by
        intro c'
        by_cases h : cellReach Cbox Cdep J c c' ∧ (c'.isRight = true → 1 ≤ gb)
        · rw [ite_eq_left h, ite_eq_left h]
          exact mul_le_mul' le_rfl (ih _ c')
        · rw [ite_eq_right h, ite_eq_right h]
      refine (add_le_add (le_refl (1 : ℝ≥0∞)) (ENNReal.tsum_le_tsum hstep)).trans ?_
      -- split the sum into event cells and good vertices
      rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
      have hXpos : (1 : ℝ≥0∞) ≤ X := hXone c
      -- the event branch
      have hevcongr : ∀ p : ℕ × Lattice d,
          (if cellReach Cbox Cdep J c (Sum.inl p) ∧
              ((Sum.inl p : CrossCell d).isRight = true → 1 ≤ gb) then
            cellWeight d Cdep Cprob cprob q (Sum.inl p) *
              (2 * (((cellRadius Cbox Cdep (Sum.inl p) + 1) ^ d : ℕ) : ℝ≥0∞) *
                A ^ (gb - (if (Sum.inl p : CrossCell d).isRight = true then 1 else 0)))
          else 0) =
          (if cellReach Cbox Cdep J c (Sum.inl p) then
            cellWeight d Cdep Cprob cprob q (Sum.inl p) *
              (2 * A ^ gb * (((cellRadius Cbox Cdep (Sum.inl p) + 1) ^ d : ℕ) : ℝ≥0∞))
          else 0) := by
        intro p
        refine if_congr (by simp) ?_ rfl
        have hd : (if (Sum.inl p : CrossCell d).isRight = true then 1 else 0) = 0 := rfl
        rw [hd, Nat.sub_zero]
        ring
      have hev := (le_of_eq (tsum_congr hevcongr)).trans
        (tsum_event_step_le Cbox Cdep J Cprob cprob q c (2 * A ^ gb))
      rcases gb with _ | m
      · -- no good vertex is allowed
        have hgdcongr : ∀ v : Lattice d,
            (if cellReach Cbox Cdep J c (Sum.inr v) ∧
                ((Sum.inr v : CrossCell d).isRight = true → 1 ≤ 0) then
              cellWeight d Cdep Cprob cprob q (Sum.inr v) *
                (2 * (((cellRadius Cbox Cdep (Sum.inr v) + 1) ^ d : ℕ) : ℝ≥0∞) *
                  A ^ (0 - (if (Sum.inr v : CrossCell d).isRight = true then 1 else 0)))
            else 0) = 0 := by
          intro v
          rw [ite_eq_right]
          rintro ⟨-, h2⟩
          exact absurd (h2 rfl) (by omega)
        rw [tsum_congr hgdcongr, tsum_zero, add_zero]
        have hEv : (∑' p : ℕ × Lattice d,
            (if cellReach Cbox Cdep J c (Sum.inl p) ∧
                ((Sum.inl p : CrossCell d).isRight = true → 1 ≤ 0) then
              cellWeight d Cdep Cprob cprob q (Sum.inl p) *
                (2 * (((cellRadius Cbox Cdep (Sum.inl p) + 1) ^ d : ℕ) : ℝ≥0∞) *
                  A ^ (0 - (if (Sum.inl p : CrossCell d).isRight = true then 1 else 0)))
            else 0)) ≤ X := by
          refine hev.trans ?_
          calc kappa * X * (2 * A ^ 0) * pival = X * (2 * kappa * pival) := by ring
            _ ≤ X * 1 := by gcongr
            _ = X := mul_one X
        calc 1 + (∑' p : ℕ × Lattice d, _) ≤ X + X := add_le_add hXpos hEv
          _ = 2 * X * A ^ 0 := by rw [pow_zero]; ring
      · -- one good vertex may be spent
        have hgdcongr : ∀ v : Lattice d,
            (if cellReach Cbox Cdep J c (Sum.inr v) ∧
                ((Sum.inr v : CrossCell d).isRight = true → 1 ≤ m + 1) then
              cellWeight d Cdep Cprob cprob q (Sum.inr v) *
                (2 * (((cellRadius Cbox Cdep (Sum.inr v) + 1) ^ d : ℕ) : ℝ≥0∞) *
                  A ^ (m + 1 - (if (Sum.inr v : CrossCell d).isRight = true then 1 else 0)))
            else 0) =
            (if cellReach Cbox Cdep J c (Sum.inr v) then 2 * A ^ m else 0) := by
          intro v
          refine if_congr (by simp) ?_ rfl
          have hd : (if (Sum.inr v : CrossCell d).isRight = true then 1 else 0) = 1 := rfl
          have hw : cellWeight d Cdep Cprob cprob q (Sum.inr v) = 1 := rfl
          have hr : ((cellRadius Cbox Cdep (Sum.inr v) + 1) ^ d : ℕ) = 1 := by
            simp [cellRadius]
          rw [hd, hw, hr]
          simp
        rw [tsum_congr hgdcongr]
        have hgd := tsum_good_step_le Cbox Cdep J c (2 * A ^ m)
        have hEv : (∑' p : ℕ × Lattice d,
            (if cellReach Cbox Cdep J c (Sum.inl p) ∧
                ((Sum.inl p : CrossCell d).isRight = true → 1 ≤ m + 1) then
              cellWeight d Cdep Cprob cprob q (Sum.inl p) *
                (2 * (((cellRadius Cbox Cdep (Sum.inl p) + 1) ^ d : ℕ) : ℝ≥0∞) *
                  A ^ (m + 1 - (if (Sum.inl p : CrossCell d).isRight = true then 1 else 0)))
            else 0)) ≤ 2 * kappa * (X * A ^ m) := by
          refine hev.trans ?_
          calc kappa * X * (2 * A ^ (m + 1)) * pival
              = 8 * kappa * kappa * pival * (X * A ^ m) := by
                rw [hA, pow_succ]; ring
            _ ≤ 2 * kappa * (X * A ^ m) := by gcongr
        have hOne : (1 : ℝ≥0∞) ≤ X * A ^ m := by
          calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
            _ ≤ X * A ^ m := by
                gcongr
                exact one_le_pow₀ hAle
        have hGd : crossBranch d J * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) *
            (2 * A ^ m) ≤ 2 * kappa * (X * A ^ m) := by
          rw [← hkappa, ← hX]; ring_nf; exact le_rfl
        calc 1 + ((∑' p : ℕ × Lattice d, _) +
              ∑' v : Lattice d, (if cellReach Cbox Cdep J c (Sum.inr v) then
                2 * A ^ m else 0))
            ≤ X * A ^ m + (2 * kappa * (X * A ^ m) + 2 * kappa * (X * A ^ m)) :=
              add_le_add hOne (add_le_add hEv (hgd.trans hGd))
          _ = (1 + 4 * kappa) * (X * A ^ m) := by ring
          _ ≤ (8 * kappa) * (X * A ^ m) := by
              have h1 : (1 : ℝ≥0∞) ≤ 4 * kappa := by
                calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
                  _ ≤ 4 * kappa := mul_le_mul' (by norm_num) hk1
              have h14 : (1 : ℝ≥0∞) + 4 * kappa ≤ 8 * kappa := by
                calc (1 : ℝ≥0∞) + 4 * kappa ≤ 4 * kappa + 4 * kappa :=
                      add_le_add h1 le_rfl
                  _ = 8 * kappa := by ring
              exact mul_le_mul' h14 le_rfl
          _ = 2 * X * A ^ (m + 1) := by rw [hA, pow_succ]; ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
