import Homogenization.Geometry.TriadicCube
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A grid of equal cubes inside a centered cube

For a side `h > 0` and a centered open cube `(-L/2, L/2)^d` with `2h ≤ L`, the
grid boxes `h (k + (-1/2,1/2)^d)`, `k ∈ ℤ^d`, contained in the cube form a finite
pairwise-disjoint family whose union misses at most `L^d - (L - 2h)^d` of the
volume.  Only the boxes' coordinates are used; no counting of lattice points is
needed: the shrunken cube `(-(L/2 - h), L/2 - h)^d` is covered by the half-open
versions of the selected boxes (`k = ⌊x/h + 1/2⌋`).

The dilated triadic cube `t • openCubeSet ⟨l, k⟩` is exactly the grid box of
side `t 3^l` with index `k`.
-/

set_option autoImplicit false

open MeasureTheory Set Function Homogenization
open scoped Pointwise

noncomputable section

namespace AhomDilation

variable {d : ℕ}

/-- Open grid box of side `h` and integer index `k`. -/
def gridBox (h : ℝ) (k : Fin d → ℤ) : Set (Vec d) :=
  Set.pi Set.univ fun i => Set.Ioo (((k i : ℝ) - 1 / 2) * h) (((k i : ℝ) + 1 / 2) * h)

/-- Half-open grid box. -/
def gridBoxIco (h : ℝ) (k : Fin d → ℤ) : Set (Vec d) :=
  Set.pi Set.univ fun i => Set.Ico (((k i : ℝ) - 1 / 2) * h) (((k i : ℝ) + 1 / 2) * h)

/-- The centered open cube of side `L`. -/
def centerBox (L : ℝ) : Set (Vec d) :=
  Set.pi Set.univ fun _ => Set.Ioo (-(L / 2)) (L / 2)

open Classical in
/-- The indices of the grid boxes of side `h` inside the centered cube of side `L`. -/
def gridIndex (d : ℕ) (L h : ℝ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-⌈L / h⌉) ⌈L / h⌉).filter
    fun k => ∀ i, (|(k i : ℝ)| + 1 / 2) * h ≤ L / 2

theorem measurableSet_gridBox (h : ℝ) (k : Fin d → ℤ) : MeasurableSet (gridBox h k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem isOpen_centerBox (L : ℝ) : IsOpen (centerBox (d := d) L) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem mem_gridIndex {L h : ℝ} {k : Fin d → ℤ} (hk : k ∈ gridIndex d L h) (i : Fin d) :
    (|(k i : ℝ)| + 1 / 2) * h ≤ L / 2 := by
  classical
  unfold gridIndex at hk
  exact (Finset.mem_filter.mp hk).2 i

/-- Selected boxes lie in the centered cube. -/
theorem gridBox_subset_centerBox {L h : ℝ} (hh : 0 < h) {k : Fin d → ℤ}
    (hk : k ∈ gridIndex d L h) : gridBox h k ⊆ centerBox L := by
  intro x hx
  simp only [gridBox, centerBox, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioo] at hx ⊢
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have hb := mem_gridIndex hk i
  have ha1 : (k i : ℝ) ≤ |(k i : ℝ)| := le_abs_self _
  have ha2 : -|(k i : ℝ)| ≤ (k i : ℝ) := neg_abs_le _
  have e1 : ((k i : ℝ) + 1 / 2) * h ≤ (|(k i : ℝ)| + 1 / 2) * h :=
    mul_le_mul_of_nonneg_right (by linarith) hh.le
  have e2 : (-|(k i : ℝ)| - 1 / 2) * h ≤ ((k i : ℝ) - 1 / 2) * h :=
    mul_le_mul_of_nonneg_right (by linarith) hh.le
  constructor
  · nlinarith
  · linarith

/-- Distinct boxes of one side are disjoint. -/
theorem pairwise_disjoint_gridBox {h : ℝ} (hh : 0 < h) :
    Pairwise (Disjoint on gridBox (d := d) h) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  apply hkk'
  funext i
  simp only [gridBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hx hx'
  obtain ⟨a1, a2⟩ := hx i
  obtain ⟨b1, b2⟩ := hx' i
  have hlt1 : ((k i : ℝ) - k' i) < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hh.le]
  have hlt2 : ((k' i : ℝ) - k i) < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hh.le]
  have z1 : k i - k' i < 1 := by exact_mod_cast hlt1
  have z2 : k' i - k i < 1 := by exact_mod_cast hlt2
  omega

theorem volume_gridBox {h : ℝ} (hh : 0 ≤ h) (k : Fin d → ℤ) :
    volume (gridBox h k) = ENNReal.ofReal (h ^ d) := by
  rw [gridBox, Real.volume_pi_Ioo]
  have : ∀ i : Fin d, ((k i : ℝ) + 1 / 2) * h - ((k i : ℝ) - 1 / 2) * h = h := fun i => by
    ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hh]

theorem volume_gridBoxIco {h : ℝ} (hh : 0 ≤ h) (k : Fin d → ℤ) :
    volume (gridBoxIco h k) = ENNReal.ofReal (h ^ d) := by
  rw [gridBoxIco, Real.volume_pi_Ico]
  have : ∀ i : Fin d, ((k i : ℝ) + 1 / 2) * h - ((k i : ℝ) - 1 / 2) * h = h := fun i => by
    ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hh]

theorem volume_centerBox {L : ℝ} (hL : 0 ≤ L) :
    volume (centerBox (d := d) L) = ENNReal.ofReal (L ^ d) := by
  rw [centerBox, Real.volume_pi_Ioo]
  have : L / 2 - -(L / 2) = L := by ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hL]

/-- The shrunken cube is covered by the selected half-open boxes. -/
theorem centerBox_subset_iUnion_gridBoxIco {L h : ℝ} (hh : 0 < h) (hLh : 2 * h ≤ L) :
    centerBox (d := d) (L - 2 * h) ⊆ ⋃ k ∈ gridIndex d L h, gridBoxIco h k := by
  classical
  intro x hx
  simp only [centerBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hx
  set k : Fin d → ℤ := fun i => ⌊x i / h + 1 / 2⌋ with hkdef
  have hfl : ∀ i, ((k i : ℝ) - 1 / 2) * h ≤ x i ∧ x i < ((k i : ℝ) + 1 / 2) * h := by
    intro i
    have f1 : ((k i : ℝ)) ≤ x i / h + 1 / 2 := Int.floor_le _
    have f2 : x i / h + 1 / 2 < (k i : ℝ) + 1 := Int.lt_floor_add_one _
    have e : (x i / h) * h = x i := div_mul_cancel₀ (x i) hh.ne'
    constructor
    · have := mul_le_mul_of_nonneg_right (show (k i : ℝ) - 1 / 2 ≤ x i / h by linarith) hh.le
      linarith
    · have := mul_lt_mul_of_pos_right (show x i / h < (k i : ℝ) + 1 / 2 by linarith) hh
      linarith
  have hbd : ∀ i, (|(k i : ℝ)| + 1 / 2) * h < L / 2 := by
    intro i
    obtain ⟨g1, g2⟩ := hfl i
    obtain ⟨c1, c2⟩ := hx i
    rcases abs_cases (k i : ℝ) with ⟨ha, _⟩ | ⟨ha, _⟩
    · rw [ha]; nlinarith
    · rw [ha]; nlinarith
  refine Set.mem_biUnion (x := k) ?_ ?_
  · unfold gridIndex
    refine Finset.mem_filter.mpr ⟨?_, fun i => (hbd i).le⟩
    refine Fintype.mem_piFinset.mpr fun i => ?_
    have hL0 : 0 ≤ L := by linarith
    have habs : |(k i : ℝ)| < L / h := by
      rw [lt_div_iff₀ hh]
      have := hbd i
      nlinarith [abs_nonneg (k i : ℝ)]
    have hceil : L / h ≤ (⌈L / h⌉ : ℝ) := Int.le_ceil _
    have hz : |k i| < ⌈L / h⌉ := by
      have : ((|k i| : ℤ) : ℝ) < ((⌈L / h⌉ : ℤ) : ℝ) := by
        rw [Int.cast_abs]; linarith
      exact_mod_cast this
    rw [Finset.mem_Icc]
    constructor <;> [linarith [neg_abs_le (k i)]; linarith [le_abs_self (k i)]]
  · simp only [gridBoxIco, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico]
    exact fun i => hfl i

/-- **Volume bound for the selected boxes.** -/
theorem sub_pow_le_card_mul {L h : ℝ} (hh : 0 < h) (hLh : 2 * h ≤ L) :
    (L - 2 * h) ^ d ≤ ((gridIndex d L h).card : ℝ) * h ^ d := by
  have hL2 : 0 ≤ L - 2 * h := by linarith
  have hcov := measure_mono (μ := volume) (centerBox_subset_iUnion_gridBoxIco (d := d) hh hLh)
  have hsum := measure_biUnion_finset_le (μ := volume) (gridIndex d L h)
    (fun k => gridBoxIco (d := d) h k)
  rw [volume_centerBox hL2] at hcov
  simp only [volume_gridBoxIco hh.le, Finset.sum_const, nsmul_eq_mul] at hsum
  have h3 := hcov.trans hsum
  have hcast : ((gridIndex d L h).card : ENNReal) * ENNReal.ofReal (h ^ d) =
      ENNReal.ofReal (((gridIndex d L h).card : ℝ) * h ^ d) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hcast] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3

/-- **Exact volume of the uncovered remainder.** -/
theorem volume_centerBox_diff_toReal {L h : ℝ} (hh : 0 < h) (hL : 0 ≤ L) :
    (volume (centerBox (d := d) L \ ⋃ k ∈ gridIndex d L h, gridBox h k)).toReal =
      L ^ d - ((gridIndex d L h).card : ℝ) * h ^ d := by
  have hsub : (⋃ k ∈ gridIndex d L h, gridBox (d := d) h k) ⊆ centerBox L :=
    Set.iUnion₂_subset fun k hk => gridBox_subset_centerBox hh hk
  have hmeas : MeasurableSet (⋃ k ∈ gridIndex d L h, gridBox (d := d) h k) :=
    Finset.measurableSet_biUnion _ fun k _ => measurableSet_gridBox h k
  have hunion : volume (⋃ k ∈ gridIndex d L h, gridBox (d := d) h k) =
      ENNReal.ofReal (((gridIndex d L h).card : ℝ) * h ^ d) := by
    rw [measure_biUnion_finset (fun k _ k' _ hkk' => pairwise_disjoint_gridBox hh hkk')
      (fun k _ => measurableSet_gridBox h k)]
    simp only [volume_gridBox hh.le, Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hfin : volume (⋃ k ∈ gridIndex d L h, gridBox (d := d) h k) ≠ ⊤ := by
    rw [hunion]; exact ENNReal.ofReal_ne_top
  rw [measure_diff hsub hmeas.nullMeasurableSet hfin, hunion, volume_centerBox hL]
  have hle : ENNReal.ofReal (((gridIndex d L h).card : ℝ) * h ^ d) ≤
      ENNReal.ofReal (L ^ d) := by
    rw [← hunion, ← volume_centerBox hL]; exact measure_mono hsub
  rw [ENNReal.toReal_sub_of_le hle ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]

theorem volume_centerBox_diff_lt_top (L h : ℝ) :
    volume (centerBox (d := d) L \ ⋃ k ∈ gridIndex d L h, gridBox h k) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono Set.diff_subset) ?_
  rw [centerBox, Real.volume_pi_Ioo]
  exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top

/-! ## Identification with triadic cubes -/

theorem centerBox_eq_openCubeSet (m : ℕ) :
    centerBox (d := d) ((3 : ℝ) ^ m) = openCubeSet (originCube d (m : ℤ)) := by
  ext x
  rw [mem_openCubeSet_originCube_iff]
  simp only [centerBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, zpow_natCast]
  constructor
  · intro hx i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith
  · intro hx i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith

theorem gridBox_eq_smul_openCubeSet {t : ℝ} (ht : 0 < t) (l : ℕ) (k : Fin d → ℤ) :
    gridBox (t * (3 : ℝ) ^ l) k = t • openCubeSet (⟨(l : ℤ), k⟩ : TriadicCube d) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne']
  simp only [gridBox, openCubeSet, cubeScaleFactor, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioo, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, zpow_natCast]
  have key1 : ∀ a y : ℝ, a * (t * (3 : ℝ) ^ l) < y ↔ a * (3 : ℝ) ^ l < t⁻¹ * y := by
    intro a y
    rw [inv_mul_eq_div, lt_div_iff₀ ht]
    constructor <;> intro h <;> linarith
  have key2 : ∀ a y : ℝ, y < a * (t * (3 : ℝ) ^ l) ↔ t⁻¹ * y < a * (3 : ℝ) ^ l := by
    intro a y
    rw [inv_mul_eq_div, div_lt_iff₀ ht]
    constructor <;> intro h <;> linarith
  constructor
  · intro hx i
    obtain ⟨h1, h2⟩ := hx i
    exact ⟨(key1 _ _).mp h1, (key2 _ _).mp h2⟩
  · intro hx i
    obtain ⟨h1, h2⟩ := hx i
    exact ⟨(key1 _ _).mpr h1, (key2 _ _).mpr h2⟩

/-! ## Bernoulli -/

/-- `L^d - (L - 2h)^d ≤ 2 d h L^(d-1)`, normalized. -/
theorem one_sub_pow_le {L h : ℝ} (hh : 0 < h) (hLh : 2 * h ≤ L) :
    (L ^ d - (L - 2 * h) ^ d) / L ^ d ≤ 2 * d * h / L := by
  have hL : 0 < L := by linarith
  have hLd : 0 < L ^ d := pow_pos hL d
  have hber := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(2 * h / L) by
    have : 2 * h / L ≤ 1 := (div_le_one hL).mpr hLh
    linarith) d
  have hfrac : (L - 2 * h) ^ d / L ^ d = (1 + -(2 * h / L)) ^ d := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [sub_div, div_self hLd.ne', hfrac]
  have : (d : ℝ) * -(2 * h / L) = -(2 * d * h / L) := by ring
  linarith

end AhomDilation







