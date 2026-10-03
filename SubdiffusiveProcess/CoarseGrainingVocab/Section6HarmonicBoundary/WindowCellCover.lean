module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.WindowStepAbsorption

@[expose] public section

/-!
# The triadic cell cover of a window, with bounded overlap of the parents

`ledger/reports/provider-48-harmonic-boundary.md` §15.5 item 2 names the piece
of the boundary half that is not yet landed: *the summation over the cells of
the window* — the manuscript's `9^d` cover of `:7359-7378` run at a free cover
scale, where the projected parents `P_q` no longer sit inside one fixed cube
but have **bounded overlap**, so that

```text
∑_q ∫_{P_q} F ≤ C(d) ∫_{window} F   for every F ≥ 0 .
```

This module supplies exactly that, for the sup-norm windows of
`WindowStepAbsorption.boundaryWindow`, and nothing analytic:

* `cellIndex j p` — the index of the unique scale-`j` triadic cell containing
  `p` (the triadic lattice tiles the ambient space);
* `windowBox j x r` — the finite index box of the cells that can meet the
  window of radius `r`;
* `supWindow_subset_biUnion_cells` — the cover: the window is contained in the
  union of those cells;
* `cubeSet_cellCube_subset_supWindow` — each cell of the box lies in the window
  of radius `r + 2·3^j`;
* `card_filter_parentWindow_le` — **the overlap count**: at most `28^d` of the
  scale-`(j+2)` projected parents of the cells contain any given point.  The
  parent of a cell of scale `j` has scale `j+2` and lies in the sup-norm ball
  of radius `3^{j+3}/2` about the cell's centre
  (`Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_truncatedCube`),
  and the scale-`j` lattice points in such a ball number at most `28` per
  coordinate.

The constants are deliberately generous: only their dimension-only character
matters, since the feedback coefficient of the step row is made small by the
tile depth, not by the overlap count.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The sup-norm window of radius `r` about `x`, untruncated. -/
def supWindow (x : Vec d) (r : ℝ) : Set (Vec d) := {p : Vec d | ∀ i, |p i - x i| ≤ r}

theorem boundaryWindow_subset_supWindow (m : ℤ) (x : Vec d) (r : ℝ) :
    boundaryWindow d m x r ⊆ supWindow x r := fun _ hp => hp.1

theorem supWindow_mono {x : Vec d} {r r' : ℝ} (h : r ≤ r') :
    supWindow x r ⊆ supWindow x r' := fun _ hp i => (hp i).trans h

/-- The scale-`j` triadic cell with index `idx`. -/
def cellCube (j : ℤ) (idx : Fin d → ℤ) : TriadicCube d := ⟨j, idx⟩

@[simp] theorem cellCube_scale (j : ℤ) (idx : Fin d → ℤ) :
    (cellCube j idx).scale = j := rfl

@[simp] theorem cellCube_index (j : ℤ) (idx : Fin d → ℤ) :
    (cellCube j idx).index = idx := rfl

/-- The centre of the scale-`j` cell with index `idx`. -/
def cellCentre (j : ℤ) (idx : Fin d → ℤ) : Vec d := fun i => (idx i : ℝ) * (3 : ℝ) ^ j

theorem mem_cubeSet_cellCube_iff {j : ℤ} {idx : Fin d → ℤ} {p : Vec d} :
    p ∈ cubeSet (cellCube j idx) ↔
      ∀ i, ((idx i : ℝ) - 1 / 2) * (3 : ℝ) ^ j ≤ p i ∧
        p i < ((idx i : ℝ) + 1 / 2) * (3 : ℝ) ^ j := by
  constructor
  · intro hp i
    exact hp i
  · intro hp i
    exact hp i

/-- The index of the scale-`j` cell containing `p`. -/
def cellIndex (j : ℤ) (p : Vec d) : Fin d → ℤ :=
  fun i => ⌊p i / (3 : ℝ) ^ j + 1 / 2⌋

theorem mem_cubeSet_cellIndex (j : ℤ) (p : Vec d) :
    p ∈ cubeSet (cellCube j (cellIndex j p)) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  rw [mem_cubeSet_cellCube_iff]
  intro i
  have hfl := Int.floor_le (p i / (3 : ℝ) ^ j + 1 / 2)
  have hlt := Int.lt_floor_add_one (p i / (3 : ℝ) ^ j + 1 / 2)
  have hA : ((cellIndex j p i : ℤ) : ℝ) * (3 : ℝ) ^ j ≤ p i + 1 / 2 * (3 : ℝ) ^ j := by
    have h := mul_le_mul_of_nonneg_right hfl h3.le
    rw [add_mul, div_mul_cancel₀ _ h3.ne'] at h
    exact h
  have hB : p i + 1 / 2 * (3 : ℝ) ^ j <
      (((cellIndex j p i : ℤ) : ℝ) + 1) * (3 : ℝ) ^ j := by
    have h := mul_lt_mul_of_pos_right hlt h3
    rw [add_mul, div_mul_cancel₀ _ h3.ne'] at h
    exact h
  rw [sub_mul, add_mul]
  rw [add_mul] at hB
  constructor
  · linarith [hA]
  · linarith [hB]

/-! ## The finite index box of a window -/

/-- The finite index box containing every scale-`j` cell that meets the window
of radius `r` about `x`. -/
def windowBox (j : ℤ) (x : Vec d) (r : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc ⌈(x i - r) / (3 : ℝ) ^ j - 1 / 2⌉
    ⌊(x i + r) / (3 : ℝ) ^ j + 1 / 2⌋

theorem mem_windowBox_iff {j : ℤ} {x : Vec d} {r : ℝ} {idx : Fin d → ℤ} :
    idx ∈ windowBox j x r ↔
      ∀ i, ⌈(x i - r) / (3 : ℝ) ^ j - 1 / 2⌉ ≤ idx i ∧
        idx i ≤ ⌊(x i + r) / (3 : ℝ) ^ j + 1 / 2⌋ := by
  simp only [windowBox, Fintype.mem_piFinset, Finset.mem_Icc]

/-- Every point of the window lies in a cell of the box. -/
theorem cellIndex_mem_windowBox {j : ℤ} {x : Vec d} {r : ℝ} {p : Vec d}
    (hp : p ∈ supWindow x r) : cellIndex j p ∈ windowBox j x r := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  rw [mem_windowBox_iff]
  intro i
  have habs := abs_le.1 (hp i)
  have hmono : (x i - r) / (3 : ℝ) ^ j ≤ p i / (3 : ℝ) ^ j :=
    div_le_div_of_nonneg_right (by linarith [habs.1]) h3.le
  have hmono' : p i / (3 : ℝ) ^ j ≤ (x i + r) / (3 : ℝ) ^ j :=
    div_le_div_of_nonneg_right (by linarith [habs.2]) h3.le
  constructor
  · refine Int.ceil_le.2 ?_
    have hlt := Int.lt_floor_add_one (p i / (3 : ℝ) ^ j + 1 / 2)
    have : p i / (3 : ℝ) ^ j - 1 / 2 ≤ ((cellIndex j p i : ℤ) : ℝ) := by
      simp only [cellIndex]
      linarith
    linarith
  · refine Int.le_floor.2 ?_
    have hfl := Int.floor_le (p i / (3 : ℝ) ^ j + 1 / 2)
    simp only [cellIndex] at hfl ⊢
    linarith

theorem supWindow_subset_biUnion_cells (j : ℤ) (x : Vec d) (r : ℝ) :
    supWindow x r ⊆ ⋃ idx ∈ windowBox j x r, cubeSet (cellCube j idx) := by
  intro p hp
  exact Set.mem_biUnion (cellIndex_mem_windowBox hp) (mem_cubeSet_cellIndex j p)

/-- Every cell of the box lies in the window of radius `r + 3^j`. -/
theorem cubeSet_cellCube_subset_supWindow {j : ℤ} {x : Vec d} {r : ℝ}
    {idx : Fin d → ℤ} (hidx : idx ∈ windowBox j x r) :
    cubeSet (cellCube j idx) ⊆ supWindow x (r + (3 : ℝ) ^ j) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  rw [mem_windowBox_iff] at hidx
  intro p hp i
  rw [mem_cubeSet_cellCube_iff] at hp
  have hpi := hp i
  have hlow : ((idx i : ℤ) : ℝ) ≥ (x i - r) / (3 : ℝ) ^ j - 1 / 2 :=
    le_trans (Int.le_ceil _) (by exact_mod_cast (hidx i).1)
  have hhigh : ((idx i : ℤ) : ℝ) ≤ (x i + r) / (3 : ℝ) ^ j + 1 / 2 :=
    le_trans (by exact_mod_cast (hidx i).2) (Int.floor_le _)
  have hlow' : x i - r - 1 / 2 * (3 : ℝ) ^ j ≤ ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j := by
    have := mul_le_mul_of_nonneg_right hlow h3.le
    rw [sub_mul, div_mul_cancel₀ _ h3.ne'] at this
    linarith
  have hhigh' : ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j ≤ x i + r + 1 / 2 * (3 : ℝ) ^ j := by
    have := mul_le_mul_of_nonneg_right hhigh h3.le
    rw [add_mul, div_mul_cancel₀ _ h3.ne'] at this
    linarith
  rw [sub_mul] at hpi
  rw [add_mul] at hpi
  rw [abs_le]
  constructor <;> linarith [hpi.1, hpi.2]

/-- Distinct cells of the same scale are disjoint. -/
theorem disjoint_cellCube {j : ℤ} {idx idx' : Fin d → ℤ} (h : idx ≠ idx') :
    Disjoint (cubeSet (cellCube j idx)) (cubeSet (cellCube j idx')) :=
  disjoint_cubeSet_of_scale_eq_of_ne rfl (by
    intro hcube
    exact h (congrArg TriadicCube.index hcube))

/-! ## The overlap count of the projected parents -/

/-- **The bounded overlap.**  At most `28^d` of the scale-`j` cell centres are
within sup-norm distance `3^{j+3}/2` of any given point.  Since the projected
parent of a scale-`j` cell has scale `j + 2` and lies in that ball
(`Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_truncatedCube` at
`j + 3`), at most `28^d` of the parents contain any given point. -/
theorem card_filter_parentWindow_le (j : ℤ) (p : Vec d)
    (t : Finset (Fin d → ℤ)) :
    (t.filter (fun idx => p ∈ supWindow (cellCentre j idx)
      ((3 : ℝ) ^ (j + 3) / 2))).card ≤ 28 ^ d := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  set lo : Fin d → ℤ := fun i => ⌈p i / (3 : ℝ) ^ j - 27 / 2⌉ with hlo
  set hi : Fin d → ℤ := fun i => ⌊p i / (3 : ℝ) ^ j + 27 / 2⌋ with hhi
  have hsub : (t.filter (fun idx => p ∈ supWindow (cellCentre j idx)
      ((3 : ℝ) ^ (j + 3) / 2))) ⊆ Fintype.piFinset fun i => Finset.Icc (lo i) (hi i) := by
    intro idx hidx
    rw [Finset.mem_filter] at hidx
    have hball := hidx.2
    rw [Fintype.mem_piFinset]
    simp only [Finset.mem_Icc]
    have hkey : ∀ i, |p i / (3 : ℝ) ^ j - ((idx i : ℤ) : ℝ)| ≤ 27 / 2 := by
      intro i
      have hi' : |p i - ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j| ≤ (3 : ℝ) ^ (j + 3) / 2 := by
        simpa [cellCentre] using hball i
      have hpow : (3 : ℝ) ^ (j + 3) = 27 * (3 : ℝ) ^ j := by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
        ring
      rw [hpow] at hi'
      have hdiv : p i / (3 : ℝ) ^ j - ((idx i : ℤ) : ℝ) =
          (p i - ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j) / (3 : ℝ) ^ j := by
        field_simp
      rw [hdiv, abs_div, abs_of_pos h3, div_le_iff₀ h3]
      linarith [hi']
    intro i
    constructor
    · refine Int.ceil_le.2 ?_
      have := abs_le.1 (hkey i)
      linarith [this.2]
    · refine Int.le_floor.2 ?_
      have := abs_le.1 (hkey i)
      linarith [this.1]
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Fintype.card_piFinset]
  calc ∏ i : Fin d, (Finset.Icc (lo i) (hi i)).card
      ≤ ∏ _i : Fin d, 28 := by
        refine Finset.prod_le_prod' ?_
        intro i _
        rw [Int.card_Icc]
        have hle : hi i + 1 - lo i ≤ 28 := by
          have h1 : ((hi i : ℤ) : ℝ) ≤ p i / (3 : ℝ) ^ j + 27 / 2 := Int.floor_le _
          have h2 : p i / (3 : ℝ) ^ j - 27 / 2 ≤ ((lo i : ℤ) : ℝ) := Int.le_ceil _
          have : ((hi i : ℤ) : ℝ) - ((lo i : ℤ) : ℝ) ≤ 27 := by linarith
          have hcast : ((hi i - lo i : ℤ) : ℝ) ≤ 27 := by push_cast; linarith
          have : hi i - lo i ≤ 27 := by exact_mod_cast hcast
          omega
        omega
    _ = 28 ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]


/-! ## The two summation inequalities -/

theorem measurableSet_supWindow (x : Vec d) (r : ℝ) :
    MeasurableSet (supWindow x r) := by
  have : supWindow x r = ⋂ i : Fin d, {p : Vec d | |p i - x i| ≤ r} := by
    ext p
    simp [supWindow, Set.mem_iInter]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hmeas : Measurable fun p : Vec d => |p i - x i| := by
    fun_prop
  exact hmeas measurableSet_Iic

/-- The centre of a cell of the box is close to the window's centre, so the
whole parent ball of that cell stays in a slightly larger window. -/
theorem supWindow_cellCentre_subset_supWindow {j : ℤ} {x : Vec d} {r : ℝ}
    {idx : Fin d → ℤ} (hidx : idx ∈ windowBox j x r) :
    supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2) ⊆
      supWindow x (r + 14 * (3 : ℝ) ^ j) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hpow : (3 : ℝ) ^ (j + 3) = 27 * (3 : ℝ) ^ j := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  rw [mem_windowBox_iff] at hidx
  intro p hp i
  have hpi := abs_le.1 (hp i)
  rw [hpow] at hpi
  have hlow : ((idx i : ℤ) : ℝ) ≥ (x i - r) / (3 : ℝ) ^ j - 1 / 2 :=
    le_trans (Int.le_ceil _) (by exact_mod_cast (hidx i).1)
  have hhigh : ((idx i : ℤ) : ℝ) ≤ (x i + r) / (3 : ℝ) ^ j + 1 / 2 :=
    le_trans (by exact_mod_cast (hidx i).2) (Int.floor_le _)
  have hlow' : x i - r - 1 / 2 * (3 : ℝ) ^ j ≤ ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j := by
    have := mul_le_mul_of_nonneg_right hlow h3.le
    rw [sub_mul, div_mul_cancel₀ _ h3.ne'] at this
    linarith
  have hhigh' : ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j ≤ x i + r + 1 / 2 * (3 : ℝ) ^ j := by
    have := mul_le_mul_of_nonneg_right hhigh h3.le
    rw [add_mul, div_mul_cancel₀ _ h3.ne'] at this
    linarith
  have hcentre : (cellCentre j idx) i = ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j := rfl
  rw [hcentre] at hpi
  rw [abs_le]
  constructor <;> linarith [hpi.1, hpi.2]

/-- **The cover.**  For a nonnegative integrand the energy on the window is at
most the sum of the energies on the scale-`j` cells of its index box. -/
theorem setIntegral_supWindow_le_sum_cells (j : ℤ) (x : Vec d) (r : ℝ)
    {F : Vec d → ℝ} (hF0 : ∀ p, 0 ≤ F p)
    (hint : IntegrableOn F (supWindow x (r + (3 : ℝ) ^ j))) :
    ∫ p in supWindow x r, F p ≤
      ∑ idx ∈ windowBox j x r, ∫ p in cubeSet (cellCube j idx), F p := by
  have hcells : ∀ idx ∈ windowBox j x r,
      cubeSet (cellCube j idx) ⊆ supWindow x (r + (3 : ℝ) ^ j) :=
    fun idx hidx => cubeSet_cellCube_subset_supWindow hidx
  have hunion : (⋃ idx ∈ windowBox j x r, cubeSet (cellCube j idx)) ⊆
      supWindow x (r + (3 : ℝ) ^ j) := by
    refine Set.iUnion₂_subset fun idx hidx => hcells idx hidx
  have hbig : IntegrableOn F (⋃ idx ∈ windowBox j x r, cubeSet (cellCube j idx)) :=
    hint.mono_set hunion
  have hsplit : ∫ p in ⋃ idx ∈ windowBox j x r, cubeSet (cellCube j idx), F p =
      ∑ idx ∈ windowBox j x r, ∫ p in cubeSet (cellCube j idx), F p := by
    refine integral_biUnion_finset _ (fun idx _ => measurableSet_cubeSet _) ?_
      (fun idx hidx => hint.mono_set (hcells idx hidx))
    intro a _ b _ hab
    exact disjoint_cellCube (fun h => hab (by rw [h]))
  rw [← hsplit]
  exact setIntegral_mono_set hbig
    (Filter.Eventually.of_forall hF0)
    (HasSubset.Subset.eventuallyLE (supWindow_subset_biUnion_cells j x r))

/-- **The bounded-overlap summation.**  If each cell of the box carries a set
inside its own parent ball, the sum of the integrals over those sets is at most
`28^d` times the integral over the enlarged window. -/
theorem sum_setIntegral_parents_le (j : ℤ) (x : Vec d) (r : ℝ)
    {F : Vec d → ℝ} (hF0 : ∀ p, 0 ≤ F p)
    (S : (Fin d → ℤ) → Set (Vec d)) (hSmeas : ∀ idx, MeasurableSet (S idx))
    (hS : ∀ idx ∈ windowBox j x r,
      S idx ⊆ supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2))
    (hint : IntegrableOn F (supWindow x (r + 14 * (3 : ℝ) ^ j))) :
    ∑ idx ∈ windowBox j x r, ∫ p in S idx, F p ≤
      (28 : ℝ) ^ d * ∫ p in supWindow x (r + 14 * (3 : ℝ) ^ j), F p := by
  set W : Set (Vec d) := supWindow x (r + 14 * (3 : ℝ) ^ j) with hW
  have hWmeas : MeasurableSet W := measurableSet_supWindow _ _
  have hSW : ∀ idx ∈ windowBox j x r, S idx ⊆ W := fun idx hidx =>
    (hS idx hidx).trans (supWindow_cellCentre_subset_supWindow hidx)
  have hSint : ∀ idx ∈ windowBox j x r, IntegrableOn F (S idx) := fun idx hidx =>
    hint.mono_set (hSW idx hidx)
  have hindint : ∀ idx ∈ windowBox j x r,
      Integrable ((S idx).indicator F) :=
    fun idx hidx => (hSint idx hidx).integrable_indicator (hSmeas idx)
  have hstep1 : ∑ idx ∈ windowBox j x r, ∫ p in S idx, F p =
      ∫ p, ∑ idx ∈ windowBox j x r, (S idx).indicator F p := by
    rw [integral_finset_sum _ hindint]
    exact Finset.sum_congr rfl fun idx _ => (integral_indicator (hSmeas idx)).symm
  have hRHSint : Integrable (fun p => (28 : ℝ) ^ d * W.indicator F p) :=
    ((hint.integrable_indicator hWmeas)).const_mul _
  have hLHSint : Integrable (fun p => ∑ idx ∈ windowBox j x r,
      (S idx).indicator F p) := integrable_finset_sum _ hindint
  have hpoint : ∀ p, ∑ idx ∈ windowBox j x r, (S idx).indicator F p ≤
      (28 : ℝ) ^ d * W.indicator F p := by
    intro p
    have hsum : ∑ idx ∈ windowBox j x r, (S idx).indicator F p =
        ((windowBox j x r).filter fun idx => p ∈ S idx).card • F p := by
      rw [Finset.card_filter]
      simp only [Set.indicator_apply]
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun idx _ => by
        by_cases hp : p ∈ S idx <;> simp [hp]
    rw [hsum, nsmul_eq_mul]
    by_cases hpW : p ∈ W
    · rw [Set.indicator_of_mem hpW]
      have hcard : (((windowBox j x r).filter fun idx => p ∈ S idx).card : ℝ) ≤
          (28 : ℝ) ^ d := by
        have hsubfil : ((windowBox j x r).filter fun idx => p ∈ S idx) ⊆
            ((windowBox j x r).filter fun idx =>
              p ∈ supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2)) := by
          intro idx hidx
          rw [Finset.mem_filter] at hidx ⊢
          exact ⟨hidx.1, hS idx hidx.1 hidx.2⟩
        have := (Finset.card_le_card hsubfil).trans
          (card_filter_parentWindow_le j p (windowBox j x r))
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hcard (hF0 p)
    · have hzero : ∀ idx ∈ windowBox j x r, p ∉ S idx := fun idx hidx hmem =>
        hpW (hSW idx hidx hmem)
      have hcard0 : ((windowBox j x r).filter fun idx => p ∈ S idx) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 ?_
        intro idx hidx
        exact hzero idx hidx
      rw [hcard0, Set.indicator_of_notMem hpW]
      simp
  have hmono := integral_mono hLHSint hRHSint hpoint
  rw [hstep1]
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_indicator hWmeas]


/-! ## The window step from a per-cell row -/

/-- The number of cells of the box is at most `(2r/3^j + 2)^d`.  Multiplied by
a per-cell price proportional to the cell volume `3^{jd}` this is the window
volume, which is the normalization the step row prints. -/
theorem card_windowBox_le (j : ℤ) (x : Vec d) {r : ℝ} (hr : 0 ≤ r) :
    (((windowBox j x r).card : ℕ) : ℝ) ≤ (2 * r / (3 : ℝ) ^ j + 2) ^ d := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  rw [windowBox, Fintype.card_piFinset]
  push_cast
  rw [show ((2 : ℝ) * r / (3 : ℝ) ^ j + 2) ^ d =
      ∏ _i : Fin d, (2 * r / (3 : ℝ) ^ j + 2) by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
  refine Finset.prod_le_prod₀ (fun i _ => by positivity) ?_
  intro i _
  rw [Int.card_Icc]
  have hfl : ((⌊(x i + r) / (3 : ℝ) ^ j + 1 / 2⌋ : ℤ) : ℝ) ≤
      (x i + r) / (3 : ℝ) ^ j + 1 / 2 := Int.floor_le _
  have hce : (x i - r) / (3 : ℝ) ^ j - 1 / 2 ≤
      ((⌈(x i - r) / (3 : ℝ) ^ j - 1 / 2⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hdiff : ((⌊(x i + r) / (3 : ℝ) ^ j + 1 / 2⌋ + 1 -
      ⌈(x i - r) / (3 : ℝ) ^ j - 1 / 2⌉ : ℤ) : ℝ) ≤ 2 * r / (3 : ℝ) ^ j + 2 := by
    push_cast
    have hsplit : (x i + r) / (3 : ℝ) ^ j - (x i - r) / (3 : ℝ) ^ j =
        2 * r / (3 : ℝ) ^ j := by
      field_simp
      ring
    linarith
  have hnn : (0 : ℝ) ≤ 2 * r / (3 : ℝ) ^ j + 2 := by positivity
  set Aint : ℤ := ⌊(x i + r) / (3 : ℝ) ^ j + 1 / 2⌋ + 1 -
    ⌈(x i - r) / (3 : ℝ) ^ j - 1 / 2⌉ with hAint
  rcases le_or_gt 0 Aint with hpos | hneg
  · have hcast : ((Aint.toNat : ℕ) : ℝ) = ((Aint : ℤ) : ℝ) := by
      have := Int.toNat_of_nonneg hpos
      exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) this
    rw [hcast]
    exact hdiff
  · have hzero : Aint.toNat = 0 := Int.toNat_of_nonpos hneg.le
    rw [hzero]
    simpa using hnn



theorem setIntegral_supWindow_step_of_cellRow (j : ℤ) (x : Vec d) {rho Rr : ℝ}
    {F : Vec d → ℝ} (hF0 : ∀ p, 0 ≤ F p) {Theta price : ℝ} (hTheta : 0 ≤ Theta)
    (S : (Fin d → ℤ) → Set (Vec d)) (hSmeas : ∀ idx, MeasurableSet (S idx))
    (hSball : ∀ idx ∈ windowBox j x rho,
      S idx ⊆ supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2))
    (hrow : ∀ idx ∈ windowBox j x rho,
      ∫ p in cubeSet (cellCube j idx), F p ≤ Theta * (∫ p in S idx, F p) + price)
    (hgap : rho + 14 * (3 : ℝ) ^ j ≤ Rr)
    (hint : IntegrableOn F (supWindow x Rr)) :
    ∫ p in supWindow x rho, F p ≤
      (28 : ℝ) ^ d * Theta * (∫ p in supWindow x Rr, F p) +
        ((windowBox j x rho).card : ℝ) * price := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hsub1 : supWindow x (rho + (3 : ℝ) ^ j) ⊆ supWindow x Rr :=
    supWindow_mono (by linarith)
  have hsub2 : supWindow x (rho + 14 * (3 : ℝ) ^ j) ⊆ supWindow x Rr :=
    supWindow_mono hgap
  have hcover := setIntegral_supWindow_le_sum_cells j x rho hF0 (hint.mono_set hsub1)
  have hsumrow : ∑ idx ∈ windowBox j x rho, ∫ p in cubeSet (cellCube j idx), F p ≤
      ∑ idx ∈ windowBox j x rho, (Theta * (∫ p in S idx, F p) + price) :=
    Finset.sum_le_sum hrow
  have hsplit : ∑ idx ∈ windowBox j x rho, (Theta * (∫ p in S idx, F p) + price) =
      Theta * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, F p) +
        ((windowBox j x rho).card : ℝ) * price := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hoverlap := sum_setIntegral_parents_le j x rho hF0 S hSmeas hSball
    (hint.mono_set hsub2)
  have hmono : ∫ p in supWindow x (rho + 14 * (3 : ℝ) ^ j), F p ≤
      ∫ p in supWindow x Rr, F p :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall hF0)
      (HasSubset.Subset.eventuallyLE hsub2)
  calc ∫ p in supWindow x rho, F p
      ≤ ∑ idx ∈ windowBox j x rho, ∫ p in cubeSet (cellCube j idx), F p := hcover
    _ ≤ Theta * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, F p) +
        ((windowBox j x rho).card : ℝ) * price := hsplit ▸ hsumrow
    _ ≤ Theta * ((28 : ℝ) ^ d * (∫ p in supWindow x (rho + 14 * (3 : ℝ) ^ j), F p)) +
        ((windowBox j x rho).card : ℝ) * price :=
        add_le_add (mul_le_mul_of_nonneg_left hoverlap hTheta) le_rfl
    _ ≤ (28 : ℝ) ^ d * Theta * (∫ p in supWindow x Rr, F p) +
        ((windowBox j x rho).card : ℝ) * price := by
        have hcoef : (0 : ℝ) ≤ Theta * (28 : ℝ) ^ d := by positivity
        have := mul_le_mul_of_nonneg_left hmono hcoef
        nlinarith [this]


/-- **The window step from a per-cell row with a parent-localized price.**

The form the manuscript's cell estimate actually has (`(♣)`,
`InteriorCellAtScale.exists_interiorCellEnergy_le_parentPrices_atScale`): the
per-cell price is itself an integral over the cell's *own* projected parent —
the parent oscillation `∫_{P_q} |u − c₀|²` — and only the datum leg is a genuine
constant.  Both parent-localized terms are summed by the same bounded-overlap
count. -/
theorem setIntegral_supWindow_step_of_cellRow_two (j : ℤ) (x : Vec d)
    {rho Rr : ℝ} {F G : Vec d → ℝ} (hF0 : ∀ p, 0 ≤ F p) (hG0 : ∀ p, 0 ≤ G p)
    {Theta Acoef price : ℝ} (hTheta : 0 ≤ Theta) (hAcoef : 0 ≤ Acoef)
    (S : (Fin d → ℤ) → Set (Vec d)) (hSmeas : ∀ idx, MeasurableSet (S idx))
    (hSball : ∀ idx ∈ windowBox j x rho,
      S idx ⊆ supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2))
    (hrow : ∀ idx ∈ windowBox j x rho,
      ∫ p in cubeSet (cellCube j idx), F p ≤
        Theta * (∫ p in S idx, F p) + Acoef * (∫ p in S idx, G p) + price)
    (hgap : rho + 14 * (3 : ℝ) ^ j ≤ Rr)
    (hintF : IntegrableOn F (supWindow x Rr))
    (hintG : IntegrableOn G (supWindow x Rr)) :
    ∫ p in supWindow x rho, F p ≤
      (28 : ℝ) ^ d * Theta * (∫ p in supWindow x Rr, F p) +
        (28 : ℝ) ^ d * Acoef * (∫ p in supWindow x Rr, G p) +
        ((windowBox j x rho).card : ℝ) * price := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hsub1 : supWindow x (rho + (3 : ℝ) ^ j) ⊆ supWindow x Rr :=
    supWindow_mono (by linarith)
  have hsub2 : supWindow x (rho + 14 * (3 : ℝ) ^ j) ⊆ supWindow x Rr :=
    supWindow_mono hgap
  have hcover := setIntegral_supWindow_le_sum_cells j x rho hF0 (hintF.mono_set hsub1)
  have hsumrow : ∑ idx ∈ windowBox j x rho, ∫ p in cubeSet (cellCube j idx), F p ≤
      ∑ idx ∈ windowBox j x rho,
        (Theta * (∫ p in S idx, F p) + Acoef * (∫ p in S idx, G p) + price) :=
    Finset.sum_le_sum hrow
  have hsplit : ∑ idx ∈ windowBox j x rho,
      (Theta * (∫ p in S idx, F p) + Acoef * (∫ p in S idx, G p) + price) =
      Theta * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, F p) +
        Acoef * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, G p) +
        ((windowBox j x rho).card : ℝ) * price := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hoverlapF := sum_setIntegral_parents_le j x rho hF0 S hSmeas hSball
    (hintF.mono_set hsub2)
  have hoverlapG := sum_setIntegral_parents_le j x rho hG0 S hSmeas hSball
    (hintG.mono_set hsub2)
  have hmonoF : ∫ p in supWindow x (rho + 14 * (3 : ℝ) ^ j), F p ≤
      ∫ p in supWindow x Rr, F p :=
    setIntegral_mono_set hintF (Filter.Eventually.of_forall hF0)
      (HasSubset.Subset.eventuallyLE hsub2)
  have hmonoG : ∫ p in supWindow x (rho + 14 * (3 : ℝ) ^ j), G p ≤
      ∫ p in supWindow x Rr, G p :=
    setIntegral_mono_set hintG (Filter.Eventually.of_forall hG0)
      (HasSubset.Subset.eventuallyLE hsub2)
  have hF : Theta * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, F p) ≤
      (28 : ℝ) ^ d * Theta * (∫ p in supWindow x Rr, F p) := by
    have h1 := mul_le_mul_of_nonneg_left hoverlapF hTheta
    have h2 := mul_le_mul_of_nonneg_left hmonoF
      (by positivity : (0 : ℝ) ≤ Theta * (28 : ℝ) ^ d)
    nlinarith [h1, h2]
  have hG : Acoef * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, G p) ≤
      (28 : ℝ) ^ d * Acoef * (∫ p in supWindow x Rr, G p) := by
    have h1 := mul_le_mul_of_nonneg_left hoverlapG hAcoef
    have h2 := mul_le_mul_of_nonneg_left hmonoG
      (by positivity : (0 : ℝ) ≤ Acoef * (28 : ℝ) ^ d)
    nlinarith [h1, h2]
  calc ∫ p in supWindow x rho, F p
      ≤ ∑ idx ∈ windowBox j x rho, ∫ p in cubeSet (cellCube j idx), F p := hcover
    _ ≤ Theta * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, F p) +
        Acoef * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, G p) +
        ((windowBox j x rho).card : ℝ) * price := hsplit ▸ hsumrow
    _ ≤ (28 : ℝ) ^ d * Theta * (∫ p in supWindow x Rr, F p) +
        (28 : ℝ) ^ d * Acoef * (∫ p in supWindow x Rr, G p) +
        ((windowBox j x rho).card : ℝ) * price := by
        linarith [hF, hG]





/-- The open realization of a lattice cell is the manuscript's translated cube
at the cell's centre. -/
theorem openCubeSet_cellCube_eq_translatedCube (j : ℤ) (idx : Fin d → ℤ) :
    openCubeSet (cellCube j idx) = translatedCube d j (cellCentre j idx) := by
  ext p
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    Homogenization.mem_openCubeSet_originCube_iff]
  constructor
  · intro hp i
    have hpi : ((idx i : ℝ) - 1 / 2) * (3 : ℝ) ^ j < p i ∧
        p i < ((idx i : ℝ) + 1 / 2) * (3 : ℝ) ^ j := hp i
    have hcentre : (p - cellCentre j idx) i = p i - ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j := by
      simp [cellCentre]
    rw [hcentre, sub_mul] at *
    rw [add_mul] at hpi
    constructor
    · linarith [hpi.1]
    · linarith [hpi.2]
  · intro hp i
    have hpi := hp i
    have hcentre : (p - cellCentre j idx) i = p i - ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j := by
      simp [cellCentre]
    rw [hcentre] at hpi
    show ((idx i : ℝ) - 1 / 2) * (3 : ℝ) ^ j < p i ∧
      p i < ((idx i : ℝ) + 1 / 2) * (3 : ℝ) ^ j
    rw [sub_mul, add_mul]
    constructor
    · linarith [hpi.1]
    · linarith [hpi.2]

/-- Hence the cover's cell integrals are exactly the manuscript's cell
integrals. -/
theorem setIntegral_cubeSet_cellCube_eq_translatedCube (j : ℤ) (idx : Fin d → ℤ)
    (F : Vec d → ℝ) :
    ∫ p in cubeSet (cellCube j idx), F p =
      ∫ p in translatedCube d j (cellCentre j idx), F p := by
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    openCubeSet_cellCube_eq_translatedCube]

/-- The manuscript's projected parent of a cell centre lies in the sup-norm
ball that the overlap count uses.  With the cell scale `j` and the parent scale
`j + 2` the radius is exactly `3^{j+3}/2`. -/
theorem translatedCube_wellPlacedCentre_subset_supWindow {m k : ℤ} {q : Vec d}
    (hq : q ∈ cube d m) (hkm : k ≤ m) :
    translatedCube d k (Section6ExcessDecay.wellPlacedCentre q m k) ⊆
      supWindow q ((3 : ℝ) ^ (k + 1) / 2) := by
  intro p hp
  have hpin : p ∈ truncatedCube d m (k + 1) q := by
    have hsub := Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_truncatedCube
      (d := d) (m := m) (j := k + 1) q hq (by omega)
    exact hsub (by simpa using hp)
  intro i
  have hpq : p - q ∈ cube d (k + 1) :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hpin
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hpq
  have hi := hpq i
  have hsub : (p - q) i = p i - q i := by simp
  rw [hsub] at hi
  rw [abs_le]
  constructor <;> [linarith [hi.1]; linarith [hi.2]]


/-! ## Bounded overlap at the level of measures

The real-integral overlap bound above needs the integrand to be integrable.
The datum leg of the manuscript's cell price is a *Gagliardo double integral*,
for which the natural home is `ℝ≥0∞`; there the same overlap count holds with
no integrability and no measurability hypothesis on the integrand, because the
finite sum can be moved onto the measures. -/

section BoundedOverlap

variable {α : Type*} [MeasurableSpace α] {ι : Type*}

/-- **Bounded overlap, measure form.**  A finite family of measurable subsets of
`W` covering every point at most `N` times has `∑ μ|_{A i} ≤ N · μ|_W`. -/
theorem sum_restrict_le_of_boundedOverlap (mu : Measure α) (t : Finset ι)
    (A : ι → Set α) (W : Set α) (hA : ∀ i ∈ t, MeasurableSet (A i))
    (hW : MeasurableSet W) (hAW : ∀ i ∈ t, A i ⊆ W) (N : ℕ)
    (hcount : ∀ p, (t.filter fun i => p ∈ A i).card ≤ N) :
    ∑ i ∈ t, mu.restrict (A i) ≤ (N : ℝ≥0∞) • mu.restrict W := by
  refine Measure.le_iff.2 fun E hE => ?_
  have hLHS : (∑ i ∈ t, mu.restrict (A i)) E = ∑ i ∈ t, mu (E ∩ A i) := by
    rw [Measure.finset_sum_apply]
    exact Finset.sum_congr rfl fun i hi => Measure.restrict_apply' (hA i hi)
  have hRHS : ((N : ℝ≥0∞) • mu.restrict W) E = (N : ℝ≥0∞) * mu (E ∩ W) := by
    rw [Measure.smul_apply, Measure.restrict_apply' hW, smul_eq_mul]
  rw [hLHS, hRHS]
  have hind : ∀ i ∈ t, mu (E ∩ A i) =
      ∫⁻ p, (E ∩ A i).indicator (1 : α → ℝ≥0∞) p ∂mu := fun i hi =>
    (lintegral_indicator_one (hE.inter (hA i hi))).symm
  rw [Finset.sum_congr rfl hind, ← lintegral_finset_sum]
  · have hpoint : ∀ p, ∑ i ∈ t, (E ∩ A i).indicator (1 : α → ℝ≥0∞) p ≤
        (N : ℝ≥0∞) * (E ∩ W).indicator (1 : α → ℝ≥0∞) p := by
      intro p
      have hsum : ∑ i ∈ t, (E ∩ A i).indicator (1 : α → ℝ≥0∞) p =
          ((t.filter fun i => p ∈ E ∩ A i).card : ℝ≥0∞) := by
        rw [Finset.card_filter]
        push_cast
        exact Finset.sum_congr rfl fun i _ => by
          by_cases hp : p ∈ E ∩ A i <;> simp [hp]
      rw [hsum]
      by_cases hpE : p ∈ E
      · by_cases hpW : p ∈ W
        · rw [Set.indicator_of_mem (Set.mem_inter hpE hpW)]
          have hcards : (t.filter fun i => p ∈ E ∩ A i) ⊆ (t.filter fun i => p ∈ A i) := by
            intro i hi
            rw [Finset.mem_filter] at hi ⊢
            exact ⟨hi.1, hi.2.2⟩
          have := (Finset.card_le_card hcards).trans (hcount p)
          simpa using (Nat.cast_le (α := ℝ≥0∞)).2 this
        · have hempty : (t.filter fun i => p ∈ E ∩ A i) = ∅ := by
            refine Finset.filter_eq_empty_iff.2 fun i hi hmem => ?_
            exact hpW (hAW i hi hmem.2)
          rw [hempty]
          simp
      · have hempty : (t.filter fun i => p ∈ E ∩ A i) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun i _ hmem => hpE hmem.1
        rw [hempty]
        simp
    exact (lintegral_mono hpoint).trans (by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_indicator_one (hE.inter hW)])
  · intro i hi
    exact (measurable_one.indicator (hE.inter (hA i hi)))

/-- **Bounded overlap, `lintegral` form.**  No measurability or integrability
hypothesis on the integrand is needed. -/
theorem sum_lintegral_le_of_boundedOverlap (mu : Measure α) (t : Finset ι)
    (A : ι → Set α) (W : Set α) (hA : ∀ i ∈ t, MeasurableSet (A i))
    (hW : MeasurableSet W) (hAW : ∀ i ∈ t, A i ⊆ W) (N : ℕ)
    (hcount : ∀ p, (t.filter fun i => p ∈ A i).card ≤ N)
    (f : α → ℝ≥0∞) :
    ∑ i ∈ t, ∫⁻ p in A i, f p ∂mu ≤ (N : ℝ≥0∞) * ∫⁻ p in W, f p ∂mu := by
  rw [← lintegral_finset_sum_measure]
  calc ∫⁻ p, f p ∂(∑ i ∈ t, mu.restrict (A i))
      ≤ ∫⁻ p, f p ∂((N : ℝ≥0∞) • mu.restrict W) :=
        lintegral_mono' (sum_restrict_le_of_boundedOverlap mu t A W hA hW hAW N hcount)
          le_rfl
    _ = (N : ℝ≥0∞) * ∫⁻ p in W, f p ∂mu := by
        rw [lintegral_smul_measure, smul_eq_mul]

end BoundedOverlap


/-! ## The datum leg: bounded overlap of the Gagliardo double integrals -/

/-- The unnormalized Gagliardo double integral of the fractional kernel on a
set.  `fractionalSeminormOn` is its volume- and `s`-normalized square root. -/
def gagliardoSq (W : Set (Vec d)) (s : ℝ) (f : Vec d → Vec d) : ℝ≥0∞ :=
  ∫⁻ xy in W ×ˢ W, ‖fractionalKernel s f xy‖ₑ ^ (2 : ℝ) ∂(volume.prod volume)

/-- The frozen normalized seminorm, denormalized. -/
theorem volume_mul_fractionalSeminormOn_sq (W : Set (Vec d)) (s : ℝ)
    (f : Vec d → Vec d) (hW0 : volume W ≠ 0) (hWtop : volume W ≠ ∞) :
    volume W * fractionalSeminormOn W s f ^ 2 =
      ENNReal.ofReal s * gagliardoSq W s f := by
  rw [fractionalSeminormOn, mul_pow]
  have hsq1 : ((ENNReal.ofReal s / volume W) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) =
      ENNReal.ofReal s / volume W := by
    rw [← ENNReal.rpow_natCast ((ENNReal.ofReal s / volume W) ^ (1 / 2 : ℝ)) 2,
      ← ENNReal.rpow_mul]
    norm_num
  have hsq2 : (SubdiffusiveProcess.RawLp.eLpNorm (fractionalKernel s f) 2
      ((volume.restrict W).prod (volume.restrict W))) ^ (2 : ℕ) = gagliardoSq W s f := by
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num) (by norm_num),
      ← ENNReal.rpow_natCast ((∫⁻ xy, ‖fractionalKernel s f xy‖ₑ ^
        ((2 : ℝ≥0∞).toReal) ∂((volume.restrict W).prod (volume.restrict W))) ^
        (1 / (2 : ℝ≥0∞).toReal)) 2,
      ← ENNReal.rpow_mul]
    rw [gagliardoSq, Measure.prod_restrict]
    norm_num
  rw [hsq1, hsq2, ← mul_assoc, ENNReal.mul_div_cancel hW0 hWtop]

/-- **The datum leg of the cover summation.**  The Gagliardo double integrals of
the projected parents have the same bounded overlap `28^d` as the parents
themselves: a pair `(p, q)` in `P × P` has its first coordinate in `P`. -/
theorem sum_gagliardoSq_parents_le (j : ℤ) (x : Vec d) (rho : ℝ) (s : ℝ)
    (f : Vec d → Vec d) (S : (Fin d → ℤ) → Set (Vec d))
    (hSmeas : ∀ idx, MeasurableSet (S idx))
    (hSball : ∀ idx ∈ windowBox j x rho,
      S idx ⊆ supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2))
    (W : Set (Vec d)) (hWmeas : MeasurableSet W)
    (hSW : ∀ idx ∈ windowBox j x rho, S idx ⊆ W) :
    ∑ idx ∈ windowBox j x rho, gagliardoSq (S idx) s f ≤
      (28 : ℝ≥0∞) ^ d * gagliardoSq W s f := by
  have hcount : ∀ pq : Vec d × Vec d,
      ((windowBox j x rho).filter fun idx => pq ∈ S idx ×ˢ S idx).card ≤ 28 ^ d := by
    intro pq
    have hsubfil : ((windowBox j x rho).filter fun idx => pq ∈ S idx ×ˢ S idx) ⊆
        ((windowBox j x rho).filter fun idx =>
          pq.1 ∈ supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2)) := by
      intro idx hidx
      rw [Finset.mem_filter] at hidx ⊢
      exact ⟨hidx.1, hSball idx hidx.1 hidx.2.1⟩
    exact (Finset.card_le_card hsubfil).trans
      (card_filter_parentWindow_le j pq.1 (windowBox j x rho))
  have hoverlap := sum_lintegral_le_of_boundedOverlap
    (mu := (volume.prod volume : Measure (Vec d × Vec d)))
    (t := windowBox j x rho) (A := fun idx => S idx ×ˢ S idx) (W := W ×ˢ W)
    (fun idx _ => (hSmeas idx).prod (hSmeas idx)) (hWmeas.prod hWmeas)
    (fun idx hidx => Set.prod_mono (hSW idx hidx) (hSW idx hidx)) (28 ^ d)
    (fun pq => by simpa using hcount pq)
    (fun xy => ‖fractionalKernel s f xy‖ₑ ^ (2 : ℝ))
  simpa [gagliardoSq] using hoverlap


/-- **The datum leg, in the frozen normalization.**  Exactly the form the cover
summation needs: the per-cell datum price of `(♣)` carries
`|P_q| · [g]²_{s,P_q}`, and the sum of those over the cells of the window is at
most `28^d |W| [g]²_{s,W}` — with no volume ratio. -/
theorem sum_volume_mul_fractionalSeminormOn_sq_le (j : ℤ) (x : Vec d) (rho : ℝ)
    (s : ℝ) (f : Vec d → Vec d) (S : (Fin d → ℤ) → Set (Vec d))
    (hSmeas : ∀ idx, MeasurableSet (S idx))
    (hSball : ∀ idx ∈ windowBox j x rho,
      S idx ⊆ supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2))
    (hS0 : ∀ idx ∈ windowBox j x rho, volume (S idx) ≠ 0)
    (hStop : ∀ idx ∈ windowBox j x rho, volume (S idx) ≠ ∞)
    (W : Set (Vec d)) (hWmeas : MeasurableSet W)
    (hSW : ∀ idx ∈ windowBox j x rho, S idx ⊆ W)
    (hW0 : volume W ≠ 0) (hWtop : volume W ≠ ∞) :
    ∑ idx ∈ windowBox j x rho,
        volume (S idx) * fractionalSeminormOn (S idx) s f ^ 2 ≤
      (28 : ℝ≥0∞) ^ d * (volume W * fractionalSeminormOn W s f ^ 2) := by
  have hLHS : ∑ idx ∈ windowBox j x rho,
      volume (S idx) * fractionalSeminormOn (S idx) s f ^ 2 =
      ENNReal.ofReal s * ∑ idx ∈ windowBox j x rho, gagliardoSq (S idx) s f := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun idx hidx =>
      volume_mul_fractionalSeminormOn_sq (S idx) s f (hS0 idx hidx) (hStop idx hidx)
  rw [hLHS, volume_mul_fractionalSeminormOn_sq W s f hW0 hWtop]
  calc ENNReal.ofReal s * ∑ idx ∈ windowBox j x rho, gagliardoSq (S idx) s f
      ≤ ENNReal.ofReal s * ((28 : ℝ≥0∞) ^ d * gagliardoSq W s f) :=
        mul_le_mul_right (sum_gagliardoSq_parents_le j x rho s f S hSmeas hSball
          W hWmeas hSW) _
    _ = (28 : ℝ≥0∞) ^ d * (ENNReal.ofReal s * gagliardoSq W s f) := by ring


/-- The real-valued form of the datum leg, which is what the cover assembly
consumes.  Finiteness of the window seminorm transfers to every parent by
`Section6HarmonicApproximation.fractionalSeminormOn_mono_set`. -/
theorem sum_volume_toReal_mul_fractionalSeminormOn_toReal_sq_le (j : ℤ)
    (x : Vec d) (rho : ℝ) (s : ℝ) (f : Vec d → Vec d)
    (S : (Fin d → ℤ) → Set (Vec d)) (hSmeas : ∀ idx, MeasurableSet (S idx))
    (hSball : ∀ idx ∈ windowBox j x rho,
      S idx ⊆ supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2))
    (hS0 : ∀ idx ∈ windowBox j x rho, volume (S idx) ≠ 0)
    (hStop : ∀ idx ∈ windowBox j x rho, volume (S idx) ≠ ∞)
    (W : Set (Vec d)) (hWmeas : MeasurableSet W)
    (hSW : ∀ idx ∈ windowBox j x rho, S idx ⊆ W)
    (hW0 : volume W ≠ 0) (hWtop : volume W ≠ ∞)
    (hWfin : fractionalSeminormOn W s f ≠ ∞) :
    ∑ idx ∈ windowBox j x rho,
        (volume (S idx)).toReal * (fractionalSeminormOn (S idx) s f).toReal ^ 2 ≤
      (28 : ℝ) ^ d *
        ((volume W).toReal * (fractionalSeminormOn W s f).toReal ^ 2) := by
  have hmain := sum_volume_mul_fractionalSeminormOn_sq_le j x rho s f S hSmeas
    hSball hS0 hStop W hWmeas hSW hW0 hWtop
  have hRHSfin : (28 : ℝ≥0∞) ^ d * (volume W * fractionalSeminormOn W s f ^ 2) ≠ ∞ := by
    refine ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hWtop ?_)
    exact ENNReal.pow_ne_top hWfin
  have hterm : ∀ idx ∈ windowBox j x rho,
      volume (S idx) * fractionalSeminormOn (S idx) s f ^ 2 ≠ ∞ := by
    intro idx hidx
    refine ne_top_of_le_ne_top hRHSfin (le_trans ?_ hmain)
    exact Finset.single_le_sum (f := fun i =>
      volume (S i) * fractionalSeminormOn (S i) s f ^ 2) (fun i _ => zero_le) hidx
  have hreal := ENNReal.toReal_mono hRHSfin hmain
  rw [ENNReal.toReal_sum hterm] at hreal
  have hLHS : ∀ idx ∈ windowBox j x rho,
      (volume (S idx) * fractionalSeminormOn (S idx) s f ^ 2).toReal =
        (volume (S idx)).toReal * (fractionalSeminormOn (S idx) s f).toReal ^ 2 := by
    intro idx _
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [Finset.sum_congr rfl hLHS] at hreal
  refine hreal.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow]
  norm_num


/-- **The parent of a cell of the step row's window stays in the budget
window.**  This is the hypothesis
`translatedCube d k (wellPlacedCentre q m k) ⊆ U` of
`InteriorCellAtScale.exists_interiorCellEnergy_le_parentPrices_atScale`,
discharged for every cell centre of `boundaryWindow d m x R` with
`R ≤ 4·3ⁿ/9` and every cover scale `k ≤ n − 4`: the extreme corner reached is
`25·3ⁿ/54` against the budget window's `27·3ⁿ/54`. -/
theorem translatedCube_wellPlacedCentre_subset_truncatedCube_of_supWindow
    {m k : ℤ} {n : ℕ} {x q : Vec d} (hq : q ∈ cube d m) (hkm : k ≤ m)
    (hk : k ≤ (n : ℤ) - 4) (hqx : q ∈ supWindow x (4 * (3 : ℝ) ^ n / 9)) :
    translatedCube d k (Section6ExcessDecay.wellPlacedCentre q m k) ⊆
      truncatedCube d m (n : ℤ) x := by
  intro p hp
  have hpq : p ∈ supWindow q ((3 : ℝ) ^ (k + 1) / 2) :=
    translatedCube_wellPlacedCentre_subset_supWindow hq hkm hp
  have hdom : p ∈ cube d m :=
    Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hkm hp
  refine ⟨?_, hdom⟩
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hNpos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hmono : (3 : ℝ) ^ (k + 1) ≤ (3 : ℝ) ^ ((n : ℤ) - 3) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hval : (3 : ℝ) ^ ((n : ℤ) - 3) = (3 : ℝ) ^ n / 27 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    norm_num
  have hA := abs_le.1 (hpq i)
  have hB := abs_le.1 (hqx i)
  have hsub : (p - x) i = p i - x i := by simp
  rw [hval] at hmono
  rw [hsub, show ((3 : ℝ) ^ ((n : ℕ) : ℤ)) = (3 : ℝ) ^ n from zpow_natCast 3 n]
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hmono]


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
