/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellSummation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsLocalL2

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## 1. The mesoscopic cells and their cores -/

/-- The lattice spacing of the mesoscopic cell centres at scale `k`. -/
def mesoStep (k : ℤ) : ℝ := (3 : ℝ) ^ (k - 3)

theorem mesoStep_pos (k : ℤ) : 0 < mesoStep k := zpow_pos (by norm_num) _

theorem three_zpow_eq_mul_mesoStep (k : ℤ) : (3 : ℝ) ^ k = 27 * mesoStep k := by
  have h3 : ((3 : ℝ) ^ (3 : ℤ)) = 27 := by norm_num
  rw [mesoStep, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), h3]
  field_simp

theorem three_zpow_sub_two_eq_mul_mesoStep (k : ℤ) :
    (3 : ℝ) ^ (k - 2) = 3 * mesoStep k := by
  have h3 : ((3 : ℝ) ^ (2 : ℤ)) = 9 := by norm_num
  have h3' : ((3 : ℝ) ^ (3 : ℤ)) = 27 := by norm_num
  rw [mesoStep, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0),
    zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), h3, h3']
  field_simp
  ring

/-- The centre of the mesoscopic cell with lattice index `n`. -/
def mesoCentre (d : ℕ) (k : ℤ) (n : Fin d → ℤ) : Vec d :=
  fun i => (n i : ℝ) * mesoStep k

/-- The mesoscopic cell of index `n`: the open cube of side `3^k` centred at
`mesoCentre d k n`. -/
def mesoCell (d : ℕ) (k : ℤ) (n : Fin d → ℤ) : Set (Vec d) :=
  translateSet (mesoCentre d k n) (openCubeSet (originCube d k))

/-- The admissible Caccioppoli core of the mesoscopic cell of index `n`, taken
at the cell centre. -/
def mesoCore (d : ℕ) (k : ℤ) (n : Fin d → ℤ) : Set (Vec d) :=
  translateSet (mesoCentre d k n) (caccioppoliCoreSet (originCube d k) 0)

theorem mem_mesoCell_iff {k : ℤ} {n : Fin d → ℤ} {x : Vec d} :
    x ∈ mesoCell d k n ↔ ∀ i, |x i - mesoCentre d k n i| < (3 : ℝ) ^ k / 2 := by
  rw [mesoCell, mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff]
  constructor
  · intro hx i
    have h := hx i
    simp only [Pi.sub_apply] at h
    rw [abs_lt]
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  · intro hx i
    have h := abs_lt.1 (hx i)
    simp only [Pi.sub_apply]
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩

private theorem rpow_three_zpow' (m : ℤ) :
    Real.rpow (3 : ℝ) ((m : ℤ) : ℝ) = (3 : ℝ) ^ m :=
  Real.rpow_intCast 3 m

theorem mem_mesoCore_iff {k : ℤ} {n : Fin d → ℤ} {x : Vec d} :
    x ∈ mesoCore d k n ↔
      ∀ i, |x i - mesoCentre d k n i| < (3 : ℝ) ^ (k - 2) / 2 := by
  have hk2 : (0 : ℝ) < (3 : ℝ) ^ (k - 2) := zpow_pos (by norm_num) _
  have hlt : (3 : ℝ) ^ (k - 2) < (3 : ℝ) ^ k := by
    exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
  constructor
  · intro hx i
    have h := (mem_translateSet_iff_sub_mem.1 hx).2 i
    rw [show ((originCube d k).scale - 2 : ℤ) = k - 2 from rfl,
      rpow_three_zpow'] at h
    simpa using h
  · intro hx
    rw [mesoCore, mem_translateSet_iff_sub_mem, caccioppoliCoreSet]
    refine ⟨?_, ?_⟩
    · rw [mem_openCubeSet_originCube_iff]
      intro i
      have h := abs_lt.1 (hx i)
      simp only [Pi.sub_apply]
      exact ⟨by linarith only [h.1, hlt], by linarith only [h.2, hlt]⟩
    · intro i
      rw [show ((originCube d k).scale - 2 : ℤ) = k - 2 from rfl,
        rpow_three_zpow']
      have h := hx i
      simpa using h

theorem mesoCore_subset_mesoCell (k : ℤ) (n : Fin d → ℤ) :
    mesoCore d k n ⊆ mesoCell d k n := by
  intro x hx
  have hlt : (3 : ℝ) ^ (k - 2) < (3 : ℝ) ^ k :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  rw [mem_mesoCell_iff]
  intro i
  have h := (mem_mesoCore_iff.1 hx) i
  linarith only [h, hlt]

theorem measurableSet_mesoCell (k : ℤ) (n : Fin d → ℤ) :
    MeasurableSet (mesoCell d k n) := by
  rw [mesoCell, ← preimage_subRight_eq_translateSet]
  exact (measurable_id.sub_const _) (measurableSet_openCubeSet _)

theorem measurableSet_mesoCore (k : ℤ) (n : Fin d → ℤ) :
    MeasurableSet (mesoCore d k n) := by
  rw [mesoCore, ← preimage_subRight_eq_translateSet]
  exact (measurable_id.sub_const _) (measurableSet_caccioppoliCoreSet _ _)

/-- The admissibility hypothesis of `exists_mesoscopic_coarseEnergyBoundOn` for
the origin cube at its own centre: the half-scale cube about `0` sits inside the
cube.  This is what makes `mesoCore` an *admissible* Caccioppoli core. -/
theorem openCubeAtScale_zero_subset_openCubeSet_originCube (k : ℤ) :
    openCubeAtScale (0 : Vec d) ((originCube d k).scale - 1) ⊆
      openCubeSet (originCube d k) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h := hx i
  rw [show ((originCube d k).scale - 1 : ℤ) = k - 1 from rfl,
    rpow_three_zpow'] at h
  have hlt : (3 : ℝ) ^ (k - 1) < (3 : ℝ) ^ k :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have h' : |x i| < (3 : ℝ) ^ (k - 1) / 2 := by simpa using h
  have h'' := abs_lt.1 h'
  exact ⟨by linarith only [h''.1, hlt], by linarith only [h''.2, hlt]⟩


/-! ## 2. The finite index box, the containment, the cover and the overlap -/

theorem mem_translatedCube_iff_abs {m : ℤ} {c x : Vec d} :
    x ∈ translatedCube d m c ↔ ∀ i, |x i - c i| < (3 : ℝ) ^ m / 2 := by
  rw [mem_translatedCube_iff, cube, mem_openCubeSet_originCube_iff]
  constructor
  · intro hx i
    have h := hx i
    simp only [Pi.sub_apply] at h
    rw [abs_lt]
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  · intro hx i
    have h := abs_lt.1 (hx i)
    simp only [Pi.sub_apply]
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩

/-- The half-width available to the centre of a scale-`k` cell contained in the
scale-`m` contraction cube. -/
def mesoInnerRadius (k m : ℤ) : ℝ := (3 : ℝ) ^ m / 2 - (3 : ℝ) ^ k / 2

/-- The finite family of lattice indices whose cells lie inside
`translatedCube d m c`. -/
def mesoIndexBox (d : ℕ) (k m : ℤ) (c : Vec d) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i : Fin d =>
    Finset.Icc ⌈(c i - mesoInnerRadius k m) / mesoStep k⌉
      ⌊(c i + mesoInnerRadius k m) / mesoStep k⌋

theorem abs_mesoCentre_sub_le_of_mem_mesoIndexBox {k m : ℤ} {c : Vec d}
    {n : Fin d → ℤ} (hn : n ∈ mesoIndexBox d k m c) (i : Fin d) :
    |mesoCentre d k n i - c i| ≤ mesoInnerRadius k m := by
  have hh : 0 < mesoStep k := mesoStep_pos k
  rw [mesoIndexBox, Fintype.mem_piFinset] at hn
  have hi := Finset.mem_Icc.1 (hn i)
  have hlo : ((⌈(c i - mesoInnerRadius k m) / mesoStep k⌉ : ℤ) : ℝ) ≤ (n i : ℝ) := by
    exact_mod_cast hi.1
  have hhi : ((n i : ℤ) : ℝ) ≤ ((⌊(c i + mesoInnerRadius k m) / mesoStep k⌋ : ℤ) : ℝ) := by
    exact_mod_cast hi.2
  have hlo' : (c i - mesoInnerRadius k m) / mesoStep k ≤ (n i : ℝ) :=
    le_trans (Int.le_ceil _) hlo
  have hhi' : (n i : ℝ) ≤ (c i + mesoInnerRadius k m) / mesoStep k :=
    le_trans hhi (Int.floor_le _)
  have h1 : c i - mesoInnerRadius k m ≤ (n i : ℝ) * mesoStep k :=
    (div_le_iff₀ hh).1 hlo'
  have h2 : (n i : ℝ) * mesoStep k ≤ c i + mesoInnerRadius k m :=
    (le_div_iff₀ hh).1 hhi'
  rw [abs_le]
  exact ⟨by simp only [mesoCentre]; linarith only [h1],
    by simp only [mesoCentre]; linarith only [h2]⟩

/-- **Containment.**  Every cell of the index box sits inside the contraction
cube. -/
theorem mesoCell_subset_translatedCube {k m : ℤ} {c : Vec d} {n : Fin d → ℤ}
    (hn : n ∈ mesoIndexBox d k m c) :
    mesoCell d k n ⊆ translatedCube d m c := by
  intro x hx
  rw [mem_translatedCube_iff_abs]
  intro i
  have h1 := (mem_mesoCell_iff.1 hx) i
  have h2 := abs_mesoCentre_sub_le_of_mem_mesoIndexBox hn i
  have := abs_sub_abs_le_abs_sub (x i - c i) (mesoCentre d k n i - c i)
  have hsub : (x i - c i) - (mesoCentre d k n i - c i) = x i - mesoCentre d k n i := by
    ring
  rw [hsub] at this
  rw [mesoInnerRadius] at h2
  linarith only [this, h1, h2]

/-- The rounding index of a point. -/
def mesoRoundIndex (d : ℕ) (k : ℤ) (x : Vec d) : Fin d → ℤ :=
  fun i => round (x i / mesoStep k)

theorem abs_sub_mesoCentre_mesoRoundIndex_le (k : ℤ) (x : Vec d) (i : Fin d) :
    |x i - mesoCentre d k (mesoRoundIndex d k x) i| ≤ mesoStep k / 2 := by
  have hh : 0 < mesoStep k := mesoStep_pos k
  have h1 : x i - mesoCentre d k (mesoRoundIndex d k x) i =
      (x i / mesoStep k - ((round (x i / mesoStep k) : ℤ) : ℝ)) * mesoStep k := by
    simp only [mesoCentre, mesoRoundIndex]
    field_simp
  rw [h1, abs_mul, abs_of_pos hh]
  have h2 := abs_sub_round (x i / mesoStep k)
  nlinarith [h2, abs_nonneg (x i / mesoStep k - ((round (x i / mesoStep k) : ℤ) : ℝ))]

/-- **The cores cover.**  Every point lies in the core of the cell of its
rounding index: the lattice spacing is `3^{k-3}` and the core radius is
`3 * 3^{k-3} / 2`. -/
theorem mem_mesoCore_mesoRoundIndex (k : ℤ) (x : Vec d) :
    x ∈ mesoCore d k (mesoRoundIndex d k x) := by
  have hh : 0 < mesoStep k := mesoStep_pos k
  rw [mem_mesoCore_iff]
  intro i
  have h := abs_sub_mesoCentre_mesoRoundIndex_le k x i
  rw [three_zpow_sub_two_eq_mul_mesoStep]
  linarith only [h, hh]

/-- **The rounding index is in the box.**  For `k ≤ m - 1` the rounding index of
any point of the *shrunk* cube `translatedCube d (m-1) c` indexes a cell
contained in `translatedCube d m c`. -/
theorem mesoRoundIndex_mem_mesoIndexBox {k m : ℤ} {c : Vec d} (hkm : k ≤ m - 1)
    {x : Vec d} (hx : x ∈ translatedCube d (m - 1) c) :
    mesoRoundIndex d k x ∈ mesoIndexBox d k m c := by
  have hh : 0 < mesoStep k := mesoStep_pos k
  have hP : (0 : ℝ) < (3 : ℝ) ^ (m - 1) := zpow_pos (by norm_num) _
  have hkP : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (m - 1) :=
    zpow_le_zpow_right₀ (by norm_num) hkm
  have hstep : mesoStep k ≤ (3 : ℝ) ^ (m - 1) / 27 := by
    have : (3 : ℝ) ^ k = 27 * mesoStep k := three_zpow_eq_mul_mesoStep k
    linarith only [hkP, this]
  have hm : (3 : ℝ) ^ m = 3 * (3 : ℝ) ^ (m - 1) := by
    rw [show m = (m - 1) + 1 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  rw [mesoIndexBox, Fintype.mem_piFinset]
  intro i
  have hround := abs_sub_mesoCentre_mesoRoundIndex_le k x i
  have hxc := (mem_translatedCube_iff_abs.1 hx) i
  have hcentre : |mesoCentre d k (mesoRoundIndex d k x) i - c i| <
      mesoInnerRadius k m := by
    have hchain : |mesoCentre d k (mesoRoundIndex d k x) i - c i| ≤
        |mesoCentre d k (mesoRoundIndex d k x) i - x i| + |x i - c i| :=
      abs_sub_le _ _ _
    have habs : |mesoCentre d k (mesoRoundIndex d k x) i - x i| =
        |x i - mesoCentre d k (mesoRoundIndex d k x) i| := abs_sub_comm _ _
    rw [mesoInnerRadius, hm]
    rw [habs] at hchain
    linarith only [hchain, hround, hxc, hstep, hkP, hP]
  have hbnd := abs_lt.1 hcentre
  have hcent : mesoCentre d k (mesoRoundIndex d k x) i =
      ((mesoRoundIndex d k x i : ℤ) : ℝ) * mesoStep k := rfl
  rw [hcent] at hbnd
  refine Finset.mem_Icc.2 ⟨?_, ?_⟩
  · refine Int.ceil_le.2 ?_
    rw [div_le_iff₀ hh]
    linarith only [hbnd.1]
  · refine Int.le_floor.2 ?_
    rw [le_div_iff₀ hh]
    linarith only [hbnd.2]

/-- **The overlap bound.**  At most `27^d` cells of any family of mesoscopic
cells at scale `k` contain a given point: the cells have side `3^k = 27` lattice
steps. -/
theorem card_filter_mem_mesoCell_le (k : ℤ) (F : Finset (Fin d → ℤ)) (x : Vec d) :
    ((F.filter fun n => x ∈ mesoCell d k n).card : ℝ) ≤ 27 ^ d := by
  classical
  have hh : 0 < mesoStep k := mesoStep_pos k
  set a : Fin d → ℤ := fun i => ⌈x i / mesoStep k - 27 / 2⌉ with ha
  have hsub : (F.filter fun n => x ∈ mesoCell d k n) ⊆
      Fintype.piFinset fun i : Fin d => Finset.Icc (a i) (a i + 26) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Fintype.mem_piFinset]
    intro i
    have h := (mem_mesoCell_iff.1 hn.2) i
    have hcent : mesoCentre d k n i = ((n i : ℤ) : ℝ) * mesoStep k := rfl
    rw [hcent, three_zpow_eq_mul_mesoStep] at h
    have hbnd := abs_lt.1 h
    have hlo : x i / mesoStep k - 27 / 2 ≤ ((n i : ℤ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hh]
      linarith only [hbnd.2]
    have hhi : ((n i : ℤ) : ℝ) < x i / mesoStep k + 27 / 2 := by
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ hh]
      linarith only [hbnd.1]
    refine Finset.mem_Icc.2 ⟨Int.ceil_le.2 hlo, ?_⟩
    have hceil : x i / mesoStep k - 27 / 2 ≤ ((a i : ℤ) : ℝ) := by
      rw [ha]; exact Int.le_ceil _
    have : ((n i : ℤ) : ℝ) < ((a i : ℤ) : ℝ) + 27 := by
      linarith only [hhi, hceil]
    have hcast : n i < a i + 27 := by exact_mod_cast this
    omega
  have hcard := Finset.card_le_card hsub
  have hbox : (Fintype.piFinset fun i : Fin d => Finset.Icc (a i) (a i + 26)).card
      = 27 ^ d := by
    rw [Fintype.card_piFinset]
    have hone : ∀ i : Fin d, (Finset.Icc (a i) (a i + 26)).card = 27 := by
      intro i
      rw [Int.card_Icc]
      omega
    rw [Finset.prod_congr rfl fun i _ => hone i, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [hbox] at hcard
  exact_mod_cast hcard


/-! ## 3. The finite cover -/

/-- **The finite mesoscopic cover of a contraction cube.**

For every scale `k ≤ m - 1` there is a finite family of mesoscopic cells at
scale `k`, all contained in the contraction cube `translatedCube d m c`, whose
admissible Caccioppoli cores cover the shrunk cube `translatedCube d (m-1) c`,
and which cover any point at most `27^d` times.

This is the item P-231 §8 named as the sole remaining blocker of the coarse
per-cell contraction.  Note the covered set: the cores of cells *contained in*
`translatedCube d m c` can never cover `translatedCube d m c` itself, by
`not_mem_mesoCore_of_near_face` below. -/
theorem exists_halfGrid_cover_finset (d : ℕ) (k m : ℤ) (c : Vec d)
    (hkm : k ≤ m - 1) :
    ∃ F : Finset (Fin d → ℤ),
      (∀ n ∈ F, mesoCell d k n ⊆ translatedCube d m c) ∧
      (∀ n ∈ F, mesoCore d k n ⊆ mesoCell d k n) ∧
      (translatedCube d (m - 1) c ⊆ ⋃ n ∈ F, mesoCore d k n) ∧
      (∀ x : Vec d, ((F.filter fun n => x ∈ mesoCell d k n).card : ℝ) ≤ 27 ^ d) := by
  classical
  refine ⟨mesoIndexBox d k m c, fun n hn => mesoCell_subset_translatedCube hn,
    fun n _ => mesoCore_subset_mesoCell k n, ?_,
    fun x => card_filter_mem_mesoCell_le k _ x⟩
  intro x hx
  exact Set.mem_biUnion (mesoRoundIndex_mem_mesoIndexBox hkm hx)
    (mem_mesoCore_mesoRoundIndex k x)

/-! ## 4. The two integral legs, and the coarse energy bound -/

/-- Subadditivity of a nonnegative set integral over a finite cover. -/
theorem setIntegral_le_sum_setIntegral_of_cover {ι : Type*} (I : Finset ι)
    {A : ι → Set (Vec d)} (hAmeas : ∀ i, MeasurableSet (A i))
    {V : Set (Vec d)} (hVmeas : MeasurableSet V)
    {f : Vec d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hcover : V ⊆ ⋃ i ∈ I, A i)
    (hint : ∀ i ∈ I, IntegrableOn f (A i) volume)
    (hintV : IntegrableOn f V volume) :
    (∫ x in V, f x ∂volume) ≤ ∑ i ∈ I, ∫ x in A i, f x ∂volume := by
  classical
  have hindint : ∀ i ∈ I, Integrable ((A i).indicator f) volume :=
    fun i hi => (hint i hi).integrable_indicator (hAmeas i)
  have hVint : Integrable (V.indicator f) volume :=
    hintV.integrable_indicator hVmeas
  have hLHS : (∫ x in V, f x ∂volume) = ∫ x, V.indicator f x ∂volume :=
    (integral_indicator hVmeas).symm
  have hRHS : (∑ i ∈ I, ∫ x in A i, f x ∂volume) =
      ∫ x, ∑ i ∈ I, (A i).indicator f x ∂volume := by
    rw [integral_finset_sum _ hindint]
    exact Finset.sum_congr rfl fun i _ => (integral_indicator (hAmeas i)).symm
  have hpoint : ∀ p, V.indicator f p ≤ ∑ i ∈ I, (A i).indicator f p := by
    intro p
    have hnn : ∀ i ∈ I, 0 ≤ (A i).indicator f p := by
      intro i _
      by_cases hp : p ∈ A i
      · rw [Set.indicator_of_mem hp]; exact hf0 p
      · rw [Set.indicator_of_notMem hp]
    by_cases hpV : p ∈ V
    · obtain ⟨i, hi, hpA⟩ := Set.mem_iUnion₂.1 (hcover hpV)
      have hle : (A i).indicator f p ≤ ∑ j ∈ I, (A j).indicator f p :=
        Finset.single_le_sum hnn hi
      rw [Set.indicator_of_mem hpV, ← Set.indicator_of_mem hpA f]
      exact hle
    · rw [Set.indicator_of_notMem hpV]
      exact Finset.sum_nonneg hnn
  rw [hLHS, hRHS]
  exact integral_mono hVint (integrable_finset_sum _ hindint) hpoint

/-- Bounded-overlap summation of a nonnegative set integral. -/
theorem sum_setIntegral_le_of_overlap {ι : Type*} (I : Finset ι)
    {A : ι → Set (Vec d)} (hAmeas : ∀ i, MeasurableSet (A i))
    {W : Set (Vec d)} (hWmeas : MeasurableSet W) {N : ℝ}
    {f : Vec d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hsub : ∀ i ∈ I, A i ⊆ W)
    (hmult : ∀ p : Vec d, ((I.filter fun i => p ∈ A i).card : ℝ) ≤ N)
    (hint : IntegrableOn f W volume) :
    ∑ i ∈ I, ∫ x in A i, f x ∂volume ≤ N * ∫ x in W, f x ∂volume := by
  classical
  have hAint : ∀ i ∈ I, IntegrableOn f (A i) volume :=
    fun i hi => hint.mono_set (hsub i hi)
  have hindint : ∀ i ∈ I, Integrable ((A i).indicator f) volume :=
    fun i hi => (hAint i hi).integrable_indicator (hAmeas i)
  have hstep1 : (∑ i ∈ I, ∫ x in A i, f x ∂volume) =
      ∫ p, ∑ i ∈ I, (A i).indicator f p ∂volume := by
    rw [integral_finset_sum _ hindint]
    exact Finset.sum_congr rfl fun i _ => (integral_indicator (hAmeas i)).symm
  have hRHSint : Integrable (fun p => N * W.indicator f p) volume :=
    (hint.integrable_indicator hWmeas).const_mul _
  have hpoint : ∀ p, ∑ i ∈ I, (A i).indicator f p ≤ N * W.indicator f p := by
    intro p
    have hsum : ∑ i ∈ I, (A i).indicator f p =
        ((I.filter fun i => p ∈ A i).card) • f p := by
      rw [Finset.card_filter]
      simp only [Set.indicator_apply]
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun i _ => by by_cases hp : p ∈ A i <;> simp [hp]
    rw [hsum, nsmul_eq_mul]
    by_cases hpW : p ∈ W
    · rw [Set.indicator_of_mem hpW]
      exact mul_le_mul_of_nonneg_right (hmult p) (hf0 p)
    · have hempty : (I.filter fun i => p ∈ A i) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 ?_
        intro i hi hmem
        exact hpW (hsub i hi hmem)
      rw [hempty, Set.indicator_of_notMem hpW]
      simp
  have hmono := integral_mono (integrable_finset_sum _ hindint) hRHSint hpoint
  rw [hstep1]
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_indicator hWmeas]

theorem translatedCube_pred_subset (d : ℕ) (m : ℤ) (c : Vec d) :
    translatedCube d (m - 1) c ⊆ translatedCube d m c := by
  have h := translatedCube_subset_succ d (m - 1) c
  rwa [show (m - 1) + 1 = m by ring] at h

/-- **The energy leg of the coarse per-cell contraction.**

From the mesoscopic Caccioppoli bound on every cell of the finite cover, the
coarse energy bound at the contraction cube, in the genuine Caccioppoli shape
`V = translatedCube d (m-1) c ⊊ W = translatedCube d m c`.  The constant
degrades by exactly the overlap multiplicity `27^d`. -/
theorem coarseEnergyBoundOn_translatedCube_of_mesoCells
    {a w : Vec d → ℝ} {G : Vec d → Vec d} {k m : ℤ} {c : Vec d} {T Gam : ℝ}
    (hkm : k ≤ m - 1) (hT : 0 < T) (hGam : 0 ≤ Gam)
    (haG : ∀ x, 0 ≤ a x * vecNormSq (G x))
    (hEint : IntegrableOn (fun x => a x * vecNormSq (G x))
      (translatedCube d m c) volume)
    (hMint : IntegrableOn (fun x => w x ^ 2) (translatedCube d m c) volume)
    (hcell : ∀ n ∈ mesoIndexBox d k m c,
      CoarseEnergyBoundOn a (mesoCell d k n) (mesoCore d k n) w G T Gam) :
    CoarseEnergyBoundOn a (translatedCube d m c) (translatedCube d (m - 1) c)
      w G T (Gam * 27 ^ d) := by
  classical
  have hWmeas : MeasurableSet (translatedCube d m c) :=
    (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube d m c).isOpen.measurableSet
  have hVmeas : MeasurableSet (translatedCube d (m - 1) c) :=
    (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube d (m - 1) c).isOpen.measurableSet
  have hcellW : ∀ n ∈ mesoIndexBox d k m c, mesoCell d k n ⊆ translatedCube d m c :=
    fun n hn => mesoCell_subset_translatedCube hn
  have hcoreW : ∀ n ∈ mesoIndexBox d k m c, mesoCore d k n ⊆ translatedCube d m c :=
    fun n hn => (mesoCore_subset_mesoCell k n).trans (hcellW n hn)
  have henergy : (∫ x in translatedCube d (m - 1) c,
      a x * vecNormSq (G x) ∂volume) ≤
      ∑ n ∈ mesoIndexBox d k m c, ∫ x in mesoCore d k n,
        a x * vecNormSq (G x) ∂volume := by
    refine setIntegral_le_sum_setIntegral_of_cover _
      (fun n => measurableSet_mesoCore k n) hVmeas haG ?_
      (fun n hn => hEint.mono_set (hcoreW n hn))
      (hEint.mono_set (translatedCube_pred_subset d m c))
    intro x hx
    exact Set.mem_biUnion (mesoRoundIndex_mem_mesoIndexBox hkm hx)
      (mem_mesoCore_mesoRoundIndex k x)
  have hmass : (∑ n ∈ mesoIndexBox d k m c, ∫ x in mesoCell d k n,
      w x ^ 2 ∂volume) ≤ (27 : ℝ) ^ d * ∫ x in translatedCube d m c,
        w x ^ 2 ∂volume :=
    sum_setIntegral_le_of_overlap _ (fun n => measurableSet_mesoCell k n)
      hWmeas (fun x => sq_nonneg _) hcellW
      (fun p => card_filter_mem_mesoCell_le k _ p) hMint
  exact coarseEnergyBoundOn_of_cells (mesoIndexBox d k m c) hGam hT hcell
    henergy hmass



/-! ### The cover of a general concentric ball

`Vec d` carries the sup metric, so `Metric.ball c rho` is the open cube of
half-width `rho` about `c`.  The cover of §2 works for **every** radius
`rho ≤ 3^m/2 - 3^k/2 - 3^{k-3}/2`, not only for the radius `3^{m-1}/2` of the
triadic predecessor.  This matters downstream: the gradient of the cutoff
adapted to `translatedCube d n z ⊆ translatedCube d (n+1) z` is supported in the
box of half-width `3^n`, which is **larger** than `3^{(n+1)-1}/2 = 3^n/2`, so the
intermediate set of the contraction must be a ball of radius between `3^n` and
`3^{n+1}/2`, and no triadic radius lies there. -/

theorem mem_ball_iff_abs {c x : Vec d} {rho : ℝ} (hrho : 0 < rho) :
    x ∈ Metric.ball c rho ↔ ∀ i, |x i - c i| < rho := by
  rw [Metric.mem_ball, dist_pi_lt_iff hrho]
  constructor
  · intro h i
    have := h i
    rwa [Real.dist_eq] at this
  · intro h i
    have := h i
    rwa [Real.dist_eq]

theorem mesoRoundIndex_mem_mesoIndexBox_of_ball {k m : ℤ} {c : Vec d} {rho : ℝ}
    (hrho : rho + (3 : ℝ) ^ k / 2 + mesoStep k / 2 ≤ (3 : ℝ) ^ m / 2)
    {x : Vec d} (hx : ∀ i, |x i - c i| < rho) :
    mesoRoundIndex d k x ∈ mesoIndexBox d k m c := by
  have hh : 0 < mesoStep k := mesoStep_pos k
  rw [mesoIndexBox, Fintype.mem_piFinset]
  intro i
  have hround := abs_sub_mesoCentre_mesoRoundIndex_le k x i
  have hchain : |mesoCentre d k (mesoRoundIndex d k x) i - c i| ≤
      |mesoCentre d k (mesoRoundIndex d k x) i - x i| + |x i - c i| :=
    abs_sub_le _ _ _
  rw [abs_sub_comm (mesoCentre d k (mesoRoundIndex d k x) i) (x i)] at hchain
  have hbound : |mesoCentre d k (mesoRoundIndex d k x) i - c i| <
      mesoInnerRadius k m := by
    rw [mesoInnerRadius]
    linarith only [hchain, hround, hx i, hrho]
  have hbnd := abs_lt.1 hbound
  have hcent : mesoCentre d k (mesoRoundIndex d k x) i =
      ((mesoRoundIndex d k x i : ℤ) : ℝ) * mesoStep k := rfl
  rw [hcent] at hbnd
  refine Finset.mem_Icc.2 ⟨?_, ?_⟩
  · refine Int.ceil_le.2 ?_
    rw [div_le_iff₀ hh]
    linarith only [hbnd.1]
  · refine Int.le_floor.2 ?_
    rw [le_div_iff₀ hh]
    linarith only [hbnd.2]

/-- **The energy leg on a concentric ball.**  The version of
`coarseEnergyBoundOn_translatedCube_of_mesoCells` with the intermediate set an
arbitrary concentric ball, which is what the cutoff of
`exists_smooth_translatedCube_cutoff` needs. -/
theorem coarseEnergyBoundOn_ball_of_mesoCells
    {a w : Vec d → ℝ} {G : Vec d → Vec d} {k m : ℤ} {c : Vec d} {rho T Gam : ℝ}
    (hrho0 : 0 < rho)
    (hrho : rho + (3 : ℝ) ^ k / 2 + mesoStep k / 2 ≤ (3 : ℝ) ^ m / 2)
    (hT : 0 < T) (hGam : 0 ≤ Gam)
    (haG : ∀ x, 0 ≤ a x * vecNormSq (G x))
    (hEint : IntegrableOn (fun x => a x * vecNormSq (G x))
      (translatedCube d m c) volume)
    (hMint : IntegrableOn (fun x => w x ^ 2) (translatedCube d m c) volume)
    (hcell : ∀ n ∈ mesoIndexBox d k m c,
      CoarseEnergyBoundOn a (mesoCell d k n) (mesoCore d k n) w G T Gam) :
    CoarseEnergyBoundOn a (translatedCube d m c) (Metric.ball c rho)
      w G T (Gam * 27 ^ d) := by
  classical
  have hk : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hh : 0 < mesoStep k := mesoStep_pos k
  have hWmeas : MeasurableSet (translatedCube d m c) :=
    (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube d m c).isOpen.measurableSet
  have hVsub : Metric.ball c rho ⊆ translatedCube d m c := by
    intro y hy
    rw [mem_translatedCube_iff_abs]
    intro i
    have := (mem_ball_iff_abs hrho0).1 hy i
    linarith only [this, hrho, hk, hh]
  have hcellW : ∀ n ∈ mesoIndexBox d k m c, mesoCell d k n ⊆ translatedCube d m c :=
    fun n hn => mesoCell_subset_translatedCube hn
  have hcoreW : ∀ n ∈ mesoIndexBox d k m c, mesoCore d k n ⊆ translatedCube d m c :=
    fun n hn => (mesoCore_subset_mesoCell k n).trans (hcellW n hn)
  have henergy : (∫ x in Metric.ball c rho, a x * vecNormSq (G x) ∂volume) ≤
      ∑ n ∈ mesoIndexBox d k m c, ∫ x in mesoCore d k n,
        a x * vecNormSq (G x) ∂volume := by
    refine setIntegral_le_sum_setIntegral_of_cover _
      (fun n => measurableSet_mesoCore k n) Metric.isOpen_ball.measurableSet haG ?_
      (fun n hn => hEint.mono_set (hcoreW n hn)) (hEint.mono_set hVsub)
    intro x hx
    exact Set.mem_biUnion
      (mesoRoundIndex_mem_mesoIndexBox_of_ball hrho ((mem_ball_iff_abs hrho0).1 hx))
      (mem_mesoCore_mesoRoundIndex k x)
  have hmass : (∑ n ∈ mesoIndexBox d k m c, ∫ x in mesoCell d k n,
      w x ^ 2 ∂volume) ≤ (27 : ℝ) ^ d * ∫ x in translatedCube d m c,
        w x ^ 2 ∂volume :=
    sum_setIntegral_le_of_overlap _ (fun n => measurableSet_mesoCell k n)
      hWmeas (fun x => sq_nonneg _) hcellW
      (fun p => card_filter_mem_mesoCell_le k _ p) hMint
  exact coarseEnergyBoundOn_of_cells (mesoIndexBox d k m c) hGam hT hcell
    henergy hmass

/-! ## 5. The skin obstruction at the contraction cube

No family of mesoscopic cells *contained in* the contraction cube has admissible
Caccioppoli cores covering the contraction cube itself: every such core stays at
distance at least `3^k/18` from the faces.  This is the reason §4 delivers the
coarse energy bound only in the genuine Caccioppoli shape `V ⊊ W`, and hence the
reason the per-cell contraction cannot consume the price at `V = W`. -/

private theorem update_mem_translateSet_openCubeSet {k : ℤ} (z : Vec d)
    (i : Fin d) {e : ℝ} (he0 : 0 < e) (he : e < (3 : ℝ) ^ k) :
    Function.update z i (z i + ((3 : ℝ) ^ k / 2 - e)) ∈
      translateSet z (openCubeSet (originCube d k)) := by
  have hk : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff]
  intro j
  by_cases hj : j = i
  · subst hj
    simp only [Pi.sub_apply, Function.update_self]
    constructor <;> linarith only [he0, he, hk]
  · simp only [Pi.sub_apply, Function.update_of_ne hj]
    constructor <;> linarith only [hk]

private theorem update_neg_mem_translateSet_openCubeSet {k : ℤ} (z : Vec d)
    (i : Fin d) {e : ℝ} (he0 : 0 < e) (he : e < (3 : ℝ) ^ k) :
    Function.update z i (z i - ((3 : ℝ) ^ k / 2 - e)) ∈
      translateSet z (openCubeSet (originCube d k)) := by
  have hk : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff]
  intro j
  by_cases hj : j = i
  · subst hj
    simp only [Pi.sub_apply, Function.update_self]
    constructor <;> linarith only [he0, he, hk]
  · simp only [Pi.sub_apply, Function.update_of_ne hj]
    constructor <;> linarith only [hk]

/-- A cell contained in the contraction cube has its centre well inside it. -/
theorem abs_centre_sub_lt_of_cell_subset {k m : ℤ} {c z : Vec d}
    (hcell : translateSet z (openCubeSet (originCube d k)) ⊆
      translatedCube d m c) (i : Fin d) :
    |z i - c i| < (3 : ℝ) ^ m / 2 - (3 : ℝ) ^ k / 2 + (3 : ℝ) ^ k / 54 := by
  have hk : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have he0 : (0 : ℝ) < (3 : ℝ) ^ k / 54 := by linarith only [hk]
  have he : (3 : ℝ) ^ k / 54 < (3 : ℝ) ^ k := by linarith only [hk]
  have hup := mem_translatedCube_iff_abs.1
    (hcell (update_mem_translateSet_openCubeSet (k := k) z i he0 he)) i
  have hdn := mem_translatedCube_iff_abs.1
    (hcell (update_neg_mem_translateSet_openCubeSet (k := k) z i he0 he)) i
  rw [Function.update_self] at hup hdn
  have h1 := abs_lt.1 hup
  have h2 := abs_lt.1 hdn
  rw [abs_lt]
  exact ⟨by linarith only [h2.1], by linarith only [h1.2]⟩

/-- An admissible Caccioppoli centre of the origin cube is well inside it. -/
theorem abs_admissible_centre_lt {k : ℤ} {x : Vec d}
    (hadm : openCubeAtScale x ((originCube d k).scale - 1) ⊆
      openCubeSet (originCube d k)) (i : Fin d) :
    |x i| < (3 : ℝ) ^ k / 3 + (3 : ℝ) ^ k / 27 := by
  have hk : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hk1 : (3 : ℝ) ^ (k - 1) = (3 : ℝ) ^ k / 3 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hmem : ∀ v : ℝ, |v| < (3 : ℝ) ^ (k - 1) / 2 →
      Function.update x i (x i + v) ∈
        openCubeAtScale x ((originCube d k).scale - 1) := by
    intro v hv j
    rw [show ((originCube d k).scale - 1 : ℤ) = k - 1 from rfl, rpow_three_zpow']
    by_cases hj : j = i
    · subst hj
      simpa [Function.update_self] using hv
    · simp only [Function.update_of_ne hj, sub_self, abs_zero]
      have : (0 : ℝ) < (3 : ℝ) ^ (k - 1) := zpow_pos (by norm_num) _
      linarith only [this]
  have hv1 : |(3 : ℝ) ^ k / 6 - (3 : ℝ) ^ k / 27| < (3 : ℝ) ^ (k - 1) / 2 := by
    rw [hk1, abs_lt]
    constructor <;> linarith only [hk]
  have hv2 : |-((3 : ℝ) ^ k / 6 - (3 : ℝ) ^ k / 27)| < (3 : ℝ) ^ (k - 1) / 2 := by
    rw [hk1, abs_lt]
    constructor <;> linarith only [hk]
  have hup := mem_openCubeSet_originCube_iff.1 (hadm (hmem _ hv1)) i
  have hdn := mem_openCubeSet_originCube_iff.1 (hadm (hmem _ hv2)) i
  rw [Function.update_self] at hup hdn
  rw [abs_lt]
  exact ⟨by linarith only [hdn.1], by linarith only [hup.2]⟩

/-- **The skin obstruction.**  Every admissible Caccioppoli core of a mesoscopic
cell contained in `translatedCube d m c` stays at distance at least `3^k/18`
from the faces of `translatedCube d m c`. -/
theorem admissible_core_subset_shrunk {k m : ℤ} {c z x : Vec d}
    (hcell : translateSet z (openCubeSet (originCube d k)) ⊆
      translatedCube d m c)
    (hadm : openCubeAtScale x ((originCube d k).scale - 1) ⊆
      openCubeSet (originCube d k)) :
    translateSet z (caccioppoliCoreSet (originCube d k) x) ⊆
      {y : Vec d | ∀ i, |y i - c i| < (3 : ℝ) ^ m / 2 - (3 : ℝ) ^ k / 18} := by
  intro y hy i
  have hk2 : (3 : ℝ) ^ (k - 2) = (3 : ℝ) ^ k / 9 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hcore := (mem_translateSet_iff_sub_mem.1 hy).2 i
  rw [show ((originCube d k).scale - 2 : ℤ) = k - 2 from rfl, rpow_three_zpow',
    hk2] at hcore
  have hcore' : |y i - z i - x i| < (3 : ℝ) ^ k / 18 := by
    have heq : (y - z) i - x i = y i - z i - x i := rfl
    rw [heq] at hcore
    linarith only [hcore]
  have hz := abs_centre_sub_lt_of_cell_subset hcell i
  have hx := abs_admissible_centre_lt hadm i
  have h1 := abs_lt.1 hcore'
  have h2 := abs_lt.1 hz
  have h3 := abs_lt.1 hx
  rw [abs_lt]
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]


/-- **No family of contained cells covers the contraction cube by its cores.**

The consequence of `admissible_core_subset_shrunk`: whatever family of scale-`k`
mesoscopic cells one takes inside `translatedCube d m c`, and whatever
admissible Caccioppoli centres one chooses in them, the union of the cores omits
a nonempty slab of the contraction cube.  Hence `coarseEnergyBoundOn_of_cells`
can never produce `CoarseEnergyBoundOn a W W`, only `CoarseEnergyBoundOn a W V`
with `V` a strictly smaller cube — which is what §4 delivers. -/
theorem not_subset_iUnion_admissible_core [NeZero d] {k m : ℤ} {c : Vec d}
    {ι : Type*} {z x : ι → Vec d} (hkm : k ≤ m)
    (hcell : ∀ j, translateSet (z j) (openCubeSet (originCube d k)) ⊆
      translatedCube d m c)
    (hadm : ∀ j, openCubeAtScale (x j) ((originCube d k).scale - 1) ⊆
      openCubeSet (originCube d k)) :
    ¬ (translatedCube d m c ⊆
      ⋃ j : ι, translateSet (z j) (caccioppoliCoreSet (originCube d k) (x j))) := by
  classical
  have hk : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hm : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  have hkm' : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ m := zpow_le_zpow_right₀ (by norm_num) hkm
  set i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ with hi0
  set y : Vec d := Function.update c i0 (c i0 + ((3 : ℝ) ^ m / 2 - (3 : ℝ) ^ k / 36))
    with hy
  have hyW : y ∈ translatedCube d m c := by
    rw [mem_translatedCube_iff_abs]
    intro j
    by_cases hj : j = i0
    · subst hj
      rw [hy, Function.update_self, add_sub_cancel_left, abs_lt]
      constructor <;> linarith only [hk, hm, hkm']
    · rw [hy, Function.update_of_ne hj, sub_self, abs_zero]
      linarith only [hm]
  intro hsub
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hsub hyW)
  have hshrunk := admissible_core_subset_shrunk (hcell j) (hadm j) hj i0
  rw [hy, Function.update_self, add_sub_cancel_left] at hshrunk
  have hlt := abs_lt.1 hshrunk
  linarith only [hlt.2, hk]

/-! ## 6. Enlarging the mass domain of the mesoscopic price

The coarse energy bound of §4 lives on a pair `V ⊊ W`, while the per-cube price
`mesoscopicCrossPriceEnergyOn_openCubeSet_of_massive_datum` lives on `V = W`.
This is the transfer that reconciles them: a price proved on `(V, V)` is a price
on `(W, V)` as soon as the cross term does not see `W \ V` — which is exactly
the situation when the cutoff's gradient is supported in `V`. -/
theorem mesoscopicCrossPriceEnergyOn_of_subdomain
    {a w : Vec d → ℝ} {G : Vec d → Vec d} {chi : Vec d → ℝ}
    {W V : Set (Vec d)} {t P R Sc : ℝ}
    (ht : 0 < t) (hP : 0 ≤ P) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hmass : (∫ x in V, w x ^ 2 ∂volume) ≤ ∫ x in W, w x ^ 2 ∂volume)
    (hcross : (∫ x in W, a x * chi x * w x *
        vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume) =
      ∫ x in V, a x * chi x * w x *
        vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume)
    (h : MesoscopicCrossPriceEnergyOn a V V w G chi t P R Sc) :
    MesoscopicCrossPriceEnergyOn a W V w G chi t P R Sc := by
  intro beta hbeta hbeta1
  have hbase := h beta hbeta hbeta1
  set E : ℝ := ∫ x in V, a x * vecNormSq (G x) ∂volume with hE
  set MV : ℝ := ∫ x in V, w x ^ 2 ∂volume with hMVdef
  set MW : ℝ := ∫ x in W, w x ^ 2 ∂volume with hMWdef
  have htinv : (0 : ℝ) ≤ t⁻¹ := inv_nonneg.2 ht.le
  have hstep : Sc * (t⁻¹ * MV) ≤ Sc * (t⁻¹ * MW) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass htinv) hSc
  have hle : E + Sc * (t⁻¹ * MV) ≤ E + Sc * (t⁻¹ * MW) := by linarith only [hstep]
  have hs : Real.sqrt (E + Sc * (t⁻¹ * MV)) ≤ Real.sqrt (E + Sc * (t⁻¹ * MW)) :=
    Real.sqrt_le_sqrt hle
  have hA : beta * P * (E + Sc * (t⁻¹ * MV)) ≤ beta * P * (E + Sc * (t⁻¹ * MW)) :=
    mul_le_mul_of_nonneg_left hle (mul_nonneg hbeta.le hP)
  have hc : (0 : ℝ) ≤ beta⁻¹ * R := mul_nonneg (inv_nonneg.2 hbeta.le) hR
  have h3 : beta⁻¹ * R * Real.sqrt (E + Sc * (t⁻¹ * MV)) ≤
      beta⁻¹ * R * Real.sqrt (E + Sc * (t⁻¹ * MW)) :=
    mul_le_mul_of_nonneg_left hs hc
  have hB : beta⁻¹ * R * Real.sqrt (E + Sc * (t⁻¹ * MV)) * Real.sqrt MV ≤
      beta⁻¹ * R * Real.sqrt (E + Sc * (t⁻¹ * MW)) * Real.sqrt MW :=
    mul_le_mul h3 (Real.sqrt_le_sqrt hmass) (Real.sqrt_nonneg _)
      (mul_nonneg hc (Real.sqrt_nonneg _))
  rw [hcross]
  linarith only [hbase, hA, hB]


/-! ## 7. A cutoff whose support leaves room for the cover

`exists_smooth_translatedCube_cutoff` (P-2xx, `WholeSpaceRowsLocalL2.lean`)
records only `tsupport chi ⊆ translatedCube d (n+1) z`, which is useless for
§6: the cross term must be confined to the *intermediate* set `V`, and `V` must
in turn be covered by the mesoscopic cores.  Choosing the margin of
`exists_smoothBoxCutoff` to be `3^n/4` rather than `3^n/2` confines the support
to the concentric ball of radius `(4/5) 3^n`, which by §4 is covered by the
mesoscopic cores at every scale `k ≤ n`, at the cost of a four-fold worse
gradient bound (`64/3^n` instead of `16/3^n`). -/
theorem exists_smooth_translatedCube_cutoff_ball (d : ℕ) (n : ℤ) (z : Vec d) :
    ∃ chi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ (∀ x, |chi x| ≤ 1) ∧
      (∀ x ∈ translatedCube d n z, chi x = 1) ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ Metric.ball z (4 / 5 * (3 : ℝ) ^ n) ∧
      (∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤
        (d : ℝ) * (64 / (3 : ℝ) ^ n) ^ 2) := by
  classical
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  set r : ℝ := (1 / 2 : ℝ) * 3 ^ n with hr_def
  have hr : 0 < r := by rw [hr_def]; positivity
  have hl : (0 : ℝ) < (1 / 4 : ℝ) * 3 ^ n := by positivity
  have hle : (fun i => z i - r) ≤ (fun i => z i + r) := by
    intro i; dsimp only; linarith
  obtain ⟨eta, hsmooth, hIcc, hone, hzero, _hderiv, hsq, _hvol⟩ :=
    exists_smoothBoxCutoff (fun i => z i - r) (fun i => z i + r)
      ((1 / 4 : ℝ) * 3 ^ n) hl hle
  have hsupp : ∀ x, eta x ≠ 0 →
      x ∈ Set.Icc (fun i => z i - r - (1 / 4 : ℝ) * 3 ^ n)
        (fun i => z i + r + (1 / 4 : ℝ) * 3 ^ n) := by
    intro x hx
    by_contra hmem
    exact hx (hzero x hmem)
  refine ⟨eta, hsmooth, fun x => ?_, fun x hx => ?_, ?_, ?_, fun x => ?_⟩
  · exact abs_le.2 ⟨by linarith [(hIcc x).1], (hIcc x).2⟩
  · refine hone x ?_
    rw [mem_translatedCube_iff_abs] at hx
    refine Set.mem_Icc.2 ⟨fun i => ?_, fun i => ?_⟩
    · have := abs_lt.1 (hx i)
      simp only [hr_def]
      linarith only [this.1]
    · have := abs_lt.1 (hx i)
      simp only [hr_def]
      linarith only [this.2]
  · refine HasCompactSupport.intro (K := Set.Icc
      (fun i => z i - r - (1 / 4 : ℝ) * 3 ^ n)
      (fun i => z i + r + (1 / 4 : ℝ) * 3 ^ n)) isCompact_Icc fun x hx => hzero x hx
  · refine le_trans (closure_mono (Function.support_subset_iff'.2
      fun x hx => hzero x hx)) ?_
    rw [IsClosed.closure_eq isClosed_Icc]
    intro x hx
    rw [Set.mem_Icc] at hx
    rw [mem_ball_iff_abs (by positivity)]
    intro i
    have h1 := hx.1 i
    have h2 := hx.2 i
    simp only [hr_def] at h1 h2
    rw [abs_lt]
    constructor <;> linarith only [h1, h2, h3]
  · have hbound := hsq x
    have hcalc : vecNormSq (fun i ↦ (fderiv ℝ eta x) (basisVec i)) =
        ∑ i, ((fderiv ℝ eta x) (Pi.single i 1)) ^ 2 := by
      simp [vecNormSq, vecDot, basisVec, pow_two]
    rw [hcalc]
    refine hbound.trans (le_of_eq ?_)
    have hne : ((3 : ℝ) ^ n) ≠ 0 := ne_of_gt h3
    field_simp
    ring

theorem ball_subset_translatedCube_succ (d : ℕ) (n : ℤ) (z : Vec d) :
    Metric.ball z (4 / 5 * (3 : ℝ) ^ n) ⊆ translatedCube d (n + 1) z := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hsucc : (3 : ℝ) ^ (n + 1) = 3 ^ n * 3 := zpow_add_one₀ (by norm_num) n
  intro x hx
  rw [mem_translatedCube_iff_abs]
  intro i
  have := (mem_ball_iff_abs (by positivity) ).1 hx i
  rw [hsucc]
  linarith only [this, h3]


theorem meso_radius_bound {k n : ℤ} (hkn : k ≤ n) :
    4 / 5 * (3 : ℝ) ^ n + (3 : ℝ) ^ k / 2 + mesoStep k / 2 ≤
      (3 : ℝ) ^ (n + 1) / 2 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hk : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ n := zpow_le_zpow_right₀ (by norm_num) hkn
  have hk0 : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hstep : (3 : ℝ) ^ k = 27 * mesoStep k := three_zpow_eq_mul_mesoStep k
  have hsucc : (3 : ℝ) ^ (n + 1) = 3 ^ n * 3 := zpow_add_one₀ (by norm_num) n
  rw [hsucc]
  linarith only [hk, hk0, hstep, h3]

/-- **The energy leg in the shape the per-cell contraction consumes.**

`W = translatedCube d (n+1) c` is the contraction denominator,
`S = translatedCube d n c` the contracted cube, and
`V = Metric.ball c ((4/5) 3^n)` the intermediate set, which contains the support
of the cutoff of `exists_smooth_translatedCube_cutoff_ball` and is covered by
the mesoscopic cores at every scale `k ≤ n`. -/
theorem coarseEnergyBoundOn_contraction_pair_of_mesoCells
    {a w : Vec d → ℝ} {G : Vec d → Vec d} {k n : ℤ} {c : Vec d} {T Gam : ℝ}
    (hkn : k ≤ n) (hT : 0 < T) (hGam : 0 ≤ Gam)
    (haG : ∀ x, 0 ≤ a x * vecNormSq (G x))
    (hEint : IntegrableOn (fun x => a x * vecNormSq (G x))
      (translatedCube d (n + 1) c) volume)
    (hMint : IntegrableOn (fun x => w x ^ 2) (translatedCube d (n + 1) c) volume)
    (hcell : ∀ m ∈ mesoIndexBox d k (n + 1) c,
      CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) w G T Gam) :
    CoarseEnergyBoundOn a (translatedCube d (n + 1) c)
      (Metric.ball c (4 / 5 * (3 : ℝ) ^ n)) w G T (Gam * 27 ^ d) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  exact coarseEnergyBoundOn_ball_of_mesoCells (by positivity)
    (meso_radius_bound hkn) hT hGam haG hEint hMint hcell


/-! ## 8. The per-cell input, in the cover's language

`exists_mesoscopic_coarseEnergyBoundOn_translated` (P-229) at the origin cube of
scale `k`, the cell centre as translation and the cell centre as Caccioppoli
centre: its admissibility hypothesis is
`openCubeAtScale_zero_subset_openCubeSet_originCube`, so the per-cell hypothesis
of §4 is exactly P-229's theorem with no geometric residue. -/
theorem exists_mesoscopic_coarseEnergyBoundOn_mesoCell (d : ℕ) [NeZero d] {t : ℝ}
    (ht : 0 < t) (ht2 : t < 1 / 2) :
    ∃ Ccacc Gam0 : ℝ, 0 < Ccacc ∧ 0 ≤ Gam0 ∧
      ∀ (k : ℤ) (n : Fin d → ℤ) (afam : CoeffFamily d) (a : Vec d → ℝ) (s T : ℝ)
        (u : H1Function (mesoCell d k n)),
        (∀ y, (afam.coeffOn (originCube d k)).toCoeffField y =
          scalarCoeffField (fun p => a (p + mesoCentre d k n)) y) →
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹ (mesoCell d k n) u
          (fun _ ↦ (0 : ℝ)) →
        0 < s → s < 1 → s + t < 1 → 0 < T →
        (cubeScaleFactor (originCube d k)) ^ 2 ≤
          Ch02.lambdaS (originCube d k) t afam * T →
        Ch02.lambdaS (originCube d k) t afam * T ≤
          9 * (cubeScaleFactor (originCube d k)) ^ 2 →
        CoarseEnergyBoundOn a (mesoCell d k n) (mesoCore d k n) u.toFun u.grad T
          (caccioppoliWithRHSPrefactor Ccacc (originCube d k) afam s t * Gam0) := by
  obtain ⟨Ccacc, Gam0, hC, hG, hbound⟩ :=
    exists_mesoscopic_coarseEnergyBoundOn_translated d ht ht2
  refine ⟨Ccacc, Gam0, hC, hG, ?_⟩
  intro k n afam a s T u hA hu hs hs1 hst hT hlo hhi
  exact hbound (originCube d k) afam a s T 0 (mesoCentre d k n) u hA hu hs hs1 hst
    hT (openCubeAtScale_zero_subset_openCubeSet_originCube k) hlo hhi

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
