module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowCoverSummation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## How far the manuscript clamp can move a centre -/

/-- The clamp `wellPlacedCentre` moves a coordinate by at most its excess over
the clamping gap. -/
theorem abs_wellPlacedCentre_sub_le {m k : ℤ} (hkm : k ≤ m) (q : Vec d)
    (i : Fin d) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : |q i| ≤ Section6ExcessDecay.wellPlacedHalfGap m k + t) :
    |Section6ExcessDecay.wellPlacedCentre q m k i - q i| ≤ t := by
  have hG : 0 ≤ Section6ExcessDecay.wellPlacedHalfGap m k :=
    Section6ExcessDecay.wellPlacedHalfGap_nonneg hkm
  set G : ℝ := Section6ExcessDecay.wellPlacedHalfGap m k with hGdef
  have habs := abs_le.1 ht
  show |max (-G) (min G (q i)) - q i| ≤ t
  rcases le_total (q i) (-G) with h1 | h1
  · rw [min_eq_right (h1.trans (by linarith)), max_eq_left h1, abs_le]
    constructor <;> linarith [habs.1]
  · rcases le_total (q i) G with h2 | h2
    · rw [min_eq_right h2, max_eq_right h1, sub_self, abs_zero]
      exact ht0
    · rw [min_eq_left h2, max_eq_right (by linarith), abs_le]
      constructor <;> linarith [habs.2]

/-- The manuscript's projected parent of a centre whose coordinates exceed the
clamping gap by at most `t` stays in the sup-norm ball of radius `3^k/2 + t`
about that centre. -/
theorem translatedCube_wellPlacedCentre_subset_supWindow_of_abs_le
    {m k : ℤ} (hkm : k ≤ m) {q : Vec d} {t : ℝ} (ht0 : 0 ≤ t)
    (hq : ∀ i, |q i| ≤ Section6ExcessDecay.wellPlacedHalfGap m k + t) :
    translatedCube d k (Section6ExcessDecay.wellPlacedCentre q m k) ⊆
      supWindow q ((3 : ℝ) ^ k / 2 + t) := by
  intro p hp
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    Homogenization.mem_openCubeSet_originCube_iff] at hp
  intro i
  have hi := hp i
  have hsub : (p - Section6ExcessDecay.wellPlacedCentre q m k) i =
      p i - Section6ExcessDecay.wellPlacedCentre q m k i := by simp
  rw [hsub] at hi
  have hclamp := abs_le.1 (abs_wellPlacedCentre_sub_le hkm q i ht0 (hq i))
  rw [abs_le]
  constructor <;> [linarith [hi.1, hclamp.1]; linarith [hi.2, hclamp.2]]

/-! ## The trichotomy -/

/-- The scale-`j` lattice cell of index `idx` can meet `𝔠_m`. -/
def stepRowNear (j m : ℤ) (idx : Fin d → ℤ) : Prop :=
  ∀ i, |cellCentre j idx i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m + (1 / 2 : ℝ) * (3 : ℝ) ^ j

/-- The projected parent used by the step-row cover: the manuscript's
`q̂ + 𝔠_{j+2}` for a cell that can meet `𝔠_m`, and the empty set otherwise. -/
def stepRowParent (j m : ℤ) (idx : Fin d → ℤ) : Set (Vec d) :=
  if stepRowNear (d := d) j m idx then
    translatedCube d (j + 2)
      (Section6ExcessDecay.wellPlacedCentre (cellCentre j idx) m (j + 2))
  else ∅

theorem measurableSet_stepRowParent (j m : ℤ) (idx : Fin d → ℤ) :
    MeasurableSet (stepRowParent (d := d) j m idx) := by
  rw [stepRowParent]
  split
  · exact (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube d (j + 2)
      _).isOpen.measurableSet
  · exact MeasurableSet.empty

theorem stepRowParent_subset_cube {j m : ℤ} (hkm : j + 2 ≤ m) (idx : Fin d → ℤ) :
    stepRowParent (d := d) j m idx ⊆ cube d m := by
  rw [stepRowParent]
  split
  · exact Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube _ hkm
  · exact Set.empty_subset _

/-- **The bounded-overlap hypothesis.**  Even when the cell centre lies outside
`𝔠_m` — by at most half a cell side, which is all a near cell allows — the
clamped parent stays in the ball of radius `3^{j+3}/2` about the centre.  The
clamp moves the centre by at most `3^{j+2}/2 + 3^j/2`, so the extreme reach is
`3^{j+2} + 3^j/2 = (9 + 1/2)·3^j`, against the ball's `13.5·3^j`. -/
theorem stepRowParent_subset_supWindow {j m : ℤ} (hkm : j + 2 ≤ m)
    (idx : Fin d → ℤ) :
    stepRowParent (d := d) j m idx ⊆
      supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2) := by
  rw [stepRowParent]
  split
  case isFalse => exact Set.empty_subset _
  case isTrue hnear =>
    have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
    have h2 : (3 : ℝ) ^ (j + 2) = 9 * (3 : ℝ) ^ j := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; norm_num; ring
    have h3' : (3 : ℝ) ^ (j + 3) = 27 * (3 : ℝ) ^ j := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; norm_num; ring
    set t : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ (j + 2) + (1 / 2 : ℝ) * (3 : ℝ) ^ j with ht
    have ht0 : 0 ≤ t := by rw [ht, h2]; linarith
    have hq : ∀ i, |cellCentre j idx i| ≤
        Section6ExcessDecay.wellPlacedHalfGap m (j + 2) + t := by
      intro i
      have := hnear i
      rw [Section6ExcessDecay.wellPlacedHalfGap, ht]
      linarith
    refine (translatedCube_wellPlacedCentre_subset_supWindow_of_abs_le hkm ht0
      hq).trans ?_
    refine supWindow_mono ?_
    rw [ht, h2, h3']
    linarith

/-- A far cell contributes nothing: its truncated realization is empty. -/
theorem truncatedCube_cellCentre_eq_empty_of_not_stepRowNear {j m : ℤ}
    {idx : Fin d → ℤ} (hfar : ¬ stepRowNear (d := d) j m idx) :
    truncatedCube d m j (cellCentre j idx) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hp1, hp2⟩
  refine hfar fun i => ?_
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    Homogenization.mem_openCubeSet_originCube_iff] at hp1
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hp2
  have hi := hp1 i
  have hsub : (p - cellCentre j idx) i = p i - cellCentre j idx i := by simp
  rw [hsub] at hi
  have hpi := hp2 i
  rw [abs_le]
  constructor <;> [linarith [hi.2, hpi.1]; linarith [hi.1, hpi.2]]

theorem setIntegral_truncatedCube_cellCentre_eq_zero_of_not_stepRowNear
    {j m : ℤ} {idx : Fin d → ℤ} (hfar : ¬ stepRowNear (d := d) j m idx)
    (F : Vec d → ℝ) :
    ∫ p in truncatedCube d m j (cellCentre j idx), F p = 0 := by
  rw [truncatedCube_cellCentre_eq_empty_of_not_stepRowNear hfar,
    Measure.restrict_empty, integral_zero_measure]

/-- **The triadic lattice at scale `j ≤ m` tiles `𝔠_m` exactly.**

`3^{m-j}` is an odd integer, so the faces of `𝔠_m` are faces of scale-`j`
lattice cells.  Consequently a lattice cell either has its centre in `𝔠_m` or
misses `𝔠_m` altogether — there is no cell straddling `∂𝔠_m` with its centre
outside.  This is what lets the cover assign the manuscript's projected parent
to every cell that carries any mass, with the cell centre always in the domain,
as `Section6ExcessDecay.wellPlacedCentre` and the boundary cell price require. -/
theorem truncatedCube_cellCentre_eq_empty_of_notMem_cube {j m : ℤ} (hjm : j ≤ m)
    {idx : Fin d → ℤ} (hnot : cellCentre (d := d) j idx ∉ cube d m) :
    truncatedCube d m j (cellCentre j idx) = ∅ := by
  classical
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  set e : ℕ := (m - j).toNat with hedef
  have hme : m = j + (e : ℤ) := by rw [hedef]; omega
  set N : ℤ := (3 : ℤ) ^ e with hNdef
  obtain ⟨t, ht⟩ : Odd N := by rw [hNdef]; exact Odd.pow (by decide)
  have hNval : (3 : ℝ) ^ m = (3 : ℝ) ^ j * (N : ℝ) := by
    rw [hme, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, hNdef]
    push_cast
    ring
  have htr : (N : ℝ) = 2 * (t : ℝ) + 1 := by
    have : N = 2 * t + 1 := by omega
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hp1, hp2⟩
  refine hnot ?_
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    Homogenization.mem_openCubeSet_originCube_iff] at hp1
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hp2
  have hA := hp1 i
  have hB := hp2 i
  have hsub : (p - cellCentre j idx) i = p i - ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j := rfl
  rw [hsub] at hA
  have hcell : cellCentre (d := d) j idx i = ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j := rfl
  rw [hcell, hNval] at *
  -- the two integer bounds
  have hup : ((idx i : ℤ) : ℝ) < (t : ℝ) + 1 := by
    have hlt : ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j <
        (1 / 2 : ℝ) * ((3 : ℝ) ^ j * (N : ℝ)) + (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
      linarith [hA.1, hB.2]
    rw [htr] at hlt
    exact lt_of_mul_lt_mul_right (by linarith : ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j <
      ((t : ℝ) + 1) * (3 : ℝ) ^ j) h3j.le
  have hlo : -((t : ℝ) + 1) < ((idx i : ℤ) : ℝ) := by
    have hgt : -((1 / 2 : ℝ) * ((3 : ℝ) ^ j * (N : ℝ))) - (1 / 2 : ℝ) * (3 : ℝ) ^ j <
        ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j := by
      linarith [hA.2, hB.1]
    rw [htr] at hgt
    exact lt_of_mul_lt_mul_right (by linarith : (-((t : ℝ) + 1)) * (3 : ℝ) ^ j <
      ((idx i : ℤ) : ℝ) * (3 : ℝ) ^ j) h3j.le
  have hupZ : idx i ≤ t := by exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast hup)
  have hloZ : -t ≤ idx i := by
    have : -(t + 1) < idx i := by exact_mod_cast hlo
    omega
  have hupR : ((idx i : ℤ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hupZ
  have hloR : -((t : ℝ)) ≤ ((idx i : ℤ) : ℝ) := by exact_mod_cast hloZ
  rw [htr]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hloR h3j.le]
  · nlinarith [mul_le_mul_of_nonneg_right hupR h3j.le]

/-- On the interior branch of the manuscript's dichotomy the cell centre is
automatically in the domain, which is what the committed interior collapse
requires of it. -/
theorem cellCentre_mem_cube_of_openCubeAtScale_subset {j m : ℤ}
    {idx : Fin d → ℤ}
    (hpatch : openCubeAtScale (cellCentre j idx) (j + 1) ⊆ cube d m) :
    cellCentre (d := d) j idx ∈ cube d m := by
  refine hpatch fun i => ?_
  have h3 : (0 : ℝ) < Real.rpow (3 : ℝ) (((j + 1 : ℤ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  simp only [sub_self, abs_zero]
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
