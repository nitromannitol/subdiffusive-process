module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsExterior

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.Frozen.Section8
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ### The half-spaced grid -/

/-- Half the side length of a triadic cube of scale `n`; also the spacing of
the grid of cell centres. -/
def gridHalfWidth (n : ℤ) : ℝ := (2 : ℝ)⁻¹ * (3 : ℝ) ^ n

theorem gridHalfWidth_pos (n : ℤ) : 0 < gridHalfWidth n := by
  have : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  simpa [gridHalfWidth] using by positivity

/-- The centre of the grid cell with lattice index `k`. -/
def gridCentre (d : ℕ) (n : ℤ) (k : Fin d → ℤ) : Vec d :=
  fun i ↦ (k i : ℝ) * gridHalfWidth n

/-- The lattice index of the cell obtained by rounding each coordinate. -/
def gridIndex (d : ℕ) (n : ℤ) (x : Vec d) : Fin d → ℤ :=
  fun i ↦ round (x i / gridHalfWidth n)

theorem mem_translatedCube_grid_iff {n : ℤ} {k : Fin d → ℤ} {x : Vec d} :
    x ∈ translatedCube d n (gridCentre d n k) ↔
      ∀ i, |x i - (k i : ℝ) * gridHalfWidth n| < gridHalfWidth n := by
  rw [mem_translatedCube_iff, cube, Homogenization.mem_openCubeSet_originCube_iff]
  constructor
  · intro hx i
    have h := hx i
    rw [abs_lt]
    have hd : (x - gridCentre d n k) i = x i - (k i : ℝ) * gridHalfWidth n := rfl
    rw [hd] at h
    constructor
    · have := h.1
      simp only [gridHalfWidth] at this ⊢
      linarith
    · have := h.2
      simp only [gridHalfWidth] at this ⊢
      linarith
  · intro hx i
    have h := (abs_lt.mp (hx i))
    have hd : (x - gridCentre d n k) i = x i - (k i : ℝ) * gridHalfWidth n := rfl
    rw [hd]
    simp only [gridHalfWidth] at h ⊢
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem mem_translatedCube_grid_succ_iff {n : ℤ} {k : Fin d → ℤ} {x : Vec d} :
    x ∈ translatedCube d (n + 1) (gridCentre d n k) ↔
      ∀ i, |x i - (k i : ℝ) * gridHalfWidth n| < 3 * gridHalfWidth n := by
  rw [mem_translatedCube_iff, cube, Homogenization.mem_openCubeSet_originCube_iff]
  have hpow : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  constructor
  · intro hx i
    have h := hx i
    have hd : (x - gridCentre d n k) i = x i - (k i : ℝ) * gridHalfWidth n := rfl
    rw [hd, hpow] at h
    rw [abs_lt]
    simp only [gridHalfWidth] at h ⊢
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro hx i
    have h := abs_lt.mp (hx i)
    have hd : (x - gridCentre d n k) i = x i - (k i : ℝ) * gridHalfWidth n := rfl
    rw [hd, hpow]
    simp only [gridHalfWidth] at h ⊢
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Every point lies in the cell of its rounded index: the half-spaced family
of open cubes covers `ℝ^d`. -/
theorem mem_translatedCube_gridIndex (d : ℕ) (n : ℤ) (x : Vec d) :
    x ∈ translatedCube d n (gridCentre d n (gridIndex d n x)) := by
  rw [mem_translatedCube_grid_iff]
  intro i
  have hpos := gridHalfWidth_pos n
  have hround : |x i / gridHalfWidth n - (round (x i / gridHalfWidth n) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  have hne : gridHalfWidth n ≠ 0 := ne_of_gt hpos
  have hid : x i - (gridIndex d n x i : ℝ) * gridHalfWidth n =
      (x i / gridHalfWidth n - (gridIndex d n x i : ℝ)) * gridHalfWidth n := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hpos]
  have hle : |x i / gridHalfWidth n - (gridIndex d n x i : ℝ)| ≤ 1 / 2 := hround
  nlinarith [hpos, abs_nonneg (x i / gridHalfWidth n - (gridIndex d n x i : ℝ))]

/-- The `7^d` grid indices within lattice distance `3` of `k`. -/
def gridNeighbours (d : ℕ) (k : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i ↦ Finset.Icc (k i - 3) (k i + 3)

theorem mem_gridNeighbours_iff {k k' : Fin d → ℤ} :
    k' ∈ gridNeighbours d k ↔ ∀ i, (k' i - k i).natAbs ≤ 3 := by
  rw [gridNeighbours, Fintype.mem_piFinset]
  constructor
  · intro h i
    have := Finset.mem_Icc.mp (h i)
    omega
  · intro h i
    have := h i
    exact Finset.mem_Icc.mpr (by omega)

theorem self_mem_gridNeighbours (d : ℕ) (k : Fin d → ℤ) :
    k ∈ gridNeighbours d k :=
  mem_gridNeighbours_iff.mpr fun i ↦ by simp

theorem card_gridNeighbours (d : ℕ) (k : Fin d → ℤ) :
    (gridNeighbours d k).card = 7 ^ d := by
  rw [gridNeighbours, Fintype.card_piFinset]
  have hcard : ∀ i : Fin d, (Finset.Icc (k i - 3) (k i + 3)).card = 7 := by
    intro i
    rw [Int.card_Icc]
    have hval : k i + 3 + 1 - (k i - 3) = (7 : ℤ) := by ring
    rw [hval]
    rfl
  simp [hcard]

/-- **The neighbour cover.**  The centred enlargement of a grid cell is covered
by the grid cells whose index differs by at most `3` in each coordinate. -/
theorem translatedCube_succ_subset_gridNeighbours (d : ℕ) (n : ℤ)
    (k : Fin d → ℤ) :
    translatedCube d (n + 1) (gridCentre d n k) ⊆
      ⋃ k' ∈ gridNeighbours d k, translatedCube d n (gridCentre d n k') := by
  intro x hx
  have hpos := gridHalfWidth_pos n
  have hne : gridHalfWidth n ≠ 0 := ne_of_gt hpos
  have hmem := mem_translatedCube_gridIndex d n x
  refine Set.mem_biUnion (mem_gridNeighbours_iff.mpr fun i ↦ ?_) hmem
  have hxi := mem_translatedCube_grid_succ_iff.mp hx i
  have hround : |x i / gridHalfWidth n - (gridIndex d n x i : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  have hid : x i - (k i : ℝ) * gridHalfWidth n =
      (x i / gridHalfWidth n - (k i : ℝ)) * gridHalfWidth n := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hpos] at hxi
  have hki : |x i / gridHalfWidth n - (k i : ℝ)| < 3 := by
    nlinarith [hpos, abs_nonneg (x i / gridHalfWidth n - (k i : ℝ))]
  have hdiff : |((gridIndex d n x i : ℝ)) - (k i : ℝ)| < 4 := by
    have h1 := abs_le.mp hround
    have h2 := abs_lt.mp hki
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hdiff
  have hlo' : (-4 : ℤ) < gridIndex d n x i - k i := by
    have : ((-4 : ℤ) : ℝ) < ((gridIndex d n x i - k i : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hhi' : (gridIndex d n x i - k i : ℤ) < 4 := by
    have : ((gridIndex d n x i - k i : ℤ) : ℝ) < ((4 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  omega

/-! ### The lattice sup-distance and the level grading -/

/-- The `ℓ^∞` distance on the index lattice. -/
def latDist (k k' : Fin d → ℤ) : ℕ :=
  Finset.univ.sup fun i ↦ (k i - k' i).natAbs

theorem latDist_coord_le (k k' : Fin d → ℤ) (i : Fin d) :
    (k i - k' i).natAbs ≤ latDist k k' :=
  Finset.le_sup (f := fun i ↦ (k i - k' i).natAbs) (Finset.mem_univ i)

theorem latDist_le_iff {k k' : Fin d → ℤ} {r : ℕ} :
    latDist k k' ≤ r ↔ ∀ i, (k i - k' i).natAbs ≤ r := by
  rw [latDist, Finset.sup_le_iff]
  exact ⟨fun h i ↦ h i (Finset.mem_univ i), fun h i _ ↦ h i⟩

theorem latDist_triangle (a b c : Fin d → ℤ) :
    latDist a c ≤ latDist a b + latDist b c := by
  refine latDist_le_iff.mpr fun i ↦ ?_
  have hsplit : a i - c i = (a i - b i) + (b i - c i) := by ring
  calc (a i - c i).natAbs ≤ (a i - b i).natAbs + (b i - c i).natAbs := by
        rw [hsplit]; exact Int.natAbs_add_le _ _
    _ ≤ latDist a b + latDist b c :=
        Nat.add_le_add (latDist_coord_le a b i) (latDist_coord_le b c i)

/-- The graph level of a grid cell: the lattice distance to the source block,
in units of three lattice steps. -/
def gridLevel (k0 : Fin d → ℤ) (m : ℕ) (k : Fin d → ℤ) : ℕ :=
  (latDist k k0 - m) / 3

theorem gridLevel_eq_zero_of_latDist_le {k0 k : Fin d → ℤ} {m : ℕ}
    (h : latDist k k0 ≤ m) : gridLevel k0 m k = 0 := by
  rw [gridLevel]
  omega

theorem latDist_le_of_gridLevel {k0 k : Fin d → ℤ} {m j : ℕ}
    (h : gridLevel k0 m k = j) : latDist k k0 ≤ m + 3 * j + 2 := by
  rw [gridLevel] at h
  omega

theorem le_latDist_of_gridLevel_pos {k0 k : Fin d → ℤ} {m : ℕ}
    (h : 0 < gridLevel k0 m k) : m + 3 ≤ latDist k k0 := by
  rw [gridLevel] at h
  omega

theorem gridLevel_le_succ_of_mem_gridNeighbours {k0 k k' : Fin d → ℤ} {m : ℕ}
    (h : k' ∈ gridNeighbours d k) :
    gridLevel k0 m k ≤ gridLevel k0 m k' + 1 := by
  have h3 : latDist k k' ≤ 3 :=
    latDist_le_iff.mpr fun i ↦ by
      have := mem_gridNeighbours_iff.mp h i
      omega
  have htri : latDist k k0 ≤ 3 + latDist k' k0 :=
    (latDist_triangle k k' k0).trans (Nat.add_le_add_right h3 _)
  rw [gridLevel, gridLevel]
  omega

/-! ### The level sets and their enumeration -/

/-- The lattice box of radius `r` around `k0`. -/
def gridBox (k0 : Fin d → ℤ) (r : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i ↦ Finset.Icc (k0 i - r) (k0 i + r)

theorem mem_gridBox_iff {k0 k : Fin d → ℤ} {r : ℕ} :
    k ∈ gridBox k0 r ↔ latDist k k0 ≤ r := by
  rw [gridBox, Fintype.mem_piFinset, latDist_le_iff]
  constructor
  · intro h i
    have := Finset.mem_Icc.mp (h i)
    omega
  · intro h i
    have := h i
    exact Finset.mem_Icc.mpr (by omega)

theorem card_gridBox (k0 : Fin d → ℤ) (r : ℕ) :
    (gridBox k0 r).card = (2 * r + 1) ^ d := by
  rw [gridBox, Fintype.card_piFinset]
  have hcard : ∀ i : Fin d,
      (Finset.Icc (k0 i - (r : ℤ)) (k0 i + (r : ℤ))).card = 2 * r + 1 := by
    intro i
    rw [Int.card_Icc]
    have hval : k0 i + (r : ℤ) + 1 - (k0 i - (r : ℤ)) = ((2 * r + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hval]
    exact Int.toNat_natCast _
  simp [hcard]

/-- The grid cells at graph level `j`. -/
def gridLevelSet (k0 : Fin d → ℤ) (m j : ℕ) : Finset (Fin d → ℤ) :=
  (gridBox k0 (m + 3 * j + 2)).filter fun k ↦ gridLevel k0 m k = j

theorem mem_gridLevelSet_iff {k0 k : Fin d → ℤ} {m j : ℕ} :
    k ∈ gridLevelSet k0 m j ↔ gridLevel k0 m k = j := by
  rw [gridLevelSet, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨mem_gridBox_iff.mpr (latDist_le_of_gridLevel h), h⟩

theorem card_gridLevelSet_le (k0 : Fin d → ℤ) (m j : ℕ) :
    (gridLevelSet k0 m j).card ≤ (2 * (m + 3 * j + 2) + 1) ^ d := by
  rw [← card_gridBox k0 (m + 3 * j + 2)]
  exact Finset.card_filter_le _ _

/-- The lattice index of the `i`-th cell at level `j`. -/
def gridCellIndex (k0 : Fin d → ℤ) (m j : ℕ)
    (i : Fin (gridLevelSet k0 m j).card) : Fin d → ℤ :=
  ((gridLevelSet k0 m j).equivFin.symm i : Fin d → ℤ)

theorem gridLevel_gridCellIndex (k0 : Fin d → ℤ) (m j : ℕ)
    (i : Fin (gridLevelSet k0 m j).card) :
    gridLevel k0 m (gridCellIndex k0 m j i) = j :=
  mem_gridLevelSet_iff.mp ((gridLevelSet k0 m j).equivFin.symm i).2

/-- The position of a grid cell inside the enumeration of its own level. -/
def gridFinIndex (k0 : Fin d → ℤ) (m : ℕ) (k : Fin d → ℤ) :
    Fin (gridLevelSet k0 m (gridLevel k0 m k)).card :=
  (gridLevelSet k0 m (gridLevel k0 m k)).equivFin
    ⟨k, mem_gridLevelSet_iff.mpr rfl⟩

theorem gridCellIndex_gridFinIndex (k0 : Fin d → ℤ) (m : ℕ) (k : Fin d → ℤ) :
    gridCellIndex k0 m (gridLevel k0 m k) (gridFinIndex k0 m k) = k := by
  rw [gridCellIndex, gridFinIndex, Equiv.symm_apply_apply]

/-! ### The source radius and the decay rate -/

/-- The lattice radius of the source block: every grid cell whose centred
enlargement meets `B_R(x0)` has lattice distance at most this from the cell of
`x0`. -/
def gridSourceRadius (n : ℤ) (R : ℝ) : ℕ := ⌈R / gridHalfWidth n⌉₊ + 1

/-- The graph-distance rate attached to the Euclidean radius `r`. -/
def gridDecayRate (n : ℤ) (R r : ℝ) : ℝ :=
  (r / gridHalfWidth n - (gridSourceRadius n R : ℝ) - 3) / 3

/-! ### The three geometric hypotheses -/

theorem card_gridLevelSet_le_geometric (k0 : Fin d → ℤ) {m : ℕ} (hm : 1 ≤ m)
    (j : ℕ) :
    (gridLevelSet k0 m j).card ≤ (2 * m + 5) ^ d * (2 ^ d) ^ j := by
  refine (card_gridLevelSet_le k0 m j).trans ?_
  have hpow : (2 * m + 5) ^ d * (2 ^ d) ^ j = ((2 * m + 5) * 2 ^ j) ^ d := by
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm d j]
  rw [hpow]
  refine Nat.pow_le_pow_left ?_ d
  have hj : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
  calc 2 * (m + 3 * j + 2) + 1 = 2 * m + 5 + 6 * j := by ring
    _ ≤ (2 * m + 5) * (j + 1) := by nlinarith [hm]
    _ ≤ (2 * m + 5) * 2 ^ j := Nat.mul_le_mul_left _ hj

theorem abs_sub_gridCentre_le (d : ℕ) (n : ℤ) (x : Vec d) (i : Fin d) :
    |x i - (gridIndex d n x i : ℝ) * gridHalfWidth n| ≤ gridHalfWidth n / 2 := by
  have hpos := gridHalfWidth_pos n
  have hne : gridHalfWidth n ≠ 0 := ne_of_gt hpos
  have hid : x i - (gridIndex d n x i : ℝ) * gridHalfWidth n =
      (x i / gridHalfWidth n - (gridIndex d n x i : ℝ)) * gridHalfWidth n := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hpos]
  have hround : |x i / gridHalfWidth n - (gridIndex d n x i : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  nlinarith [hpos]

theorem abs_natCast_latDist_coord {k k' : Fin d → ℤ} (i : Fin d) :
    |((k i : ℝ)) - (k' i : ℝ)| = (((k i - k' i).natAbs : ℕ) : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs]
  congr 1
  push_cast
  ring

/-- **The source separation.**  A grid cell at positive level has its centred
enlargement disjoint from the ball `B_R(x0)`. -/
theorem lt_norm_sub_of_gridLevel_pos [NeZero d] {n : ℤ} {R : ℝ}
    (x0 : Vec d) {k : Fin d → ℤ}
    (hk : 0 < gridLevel (gridIndex d n x0) (gridSourceRadius n R) k)
    {y : Vec d} (hy : y ∈ translatedCube d (n + 1) (gridCentre d n k)) :
    R < ‖y - x0‖ := by
  classical
  set w := gridHalfWidth n with hw
  have hpos : 0 < w := gridHalfWidth_pos n
  set k0 := gridIndex d n x0 with hk0
  set m := gridSourceRadius n R with hm
  have hL : m + 3 ≤ latDist k k0 := le_latDist_of_gridLevel_pos hk
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d)) Finset.univ_nonempty
      (fun i ↦ (k i - k0 i).natAbs)
  have hLi : |((k i : ℝ)) - (k0 i : ℝ)| = (latDist k k0 : ℝ) := by
    rw [abs_natCast_latDist_coord i, latDist, hi]
  have hyi := abs_lt.mp (mem_translatedCube_grid_succ_iff.mp hy i)
  have hx0i := abs_le.mp (abs_sub_gridCentre_le d n x0 i)
  have hcentres : |(k i : ℝ) * w - (k0 i : ℝ) * w| = (latDist k k0 : ℝ) * w := by
    rw [show (k i : ℝ) * w - (k0 i : ℝ) * w = ((k i : ℝ) - (k0 i : ℝ)) * w by ring,
      abs_mul, abs_of_pos hpos, hLi]
  have hLnn : (0 : ℝ) ≤ (latDist k k0 : ℝ) * w := by positivity
  have hceil : R / w ≤ ((⌈R / w⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hmR : (m : ℝ) = ((⌈R / w⌉₊ : ℕ) : ℝ) + 1 := by
    rw [hm, gridSourceRadius]
    push_cast
    ring
  have hRw : R ≤ ((m : ℝ) - 1) * w := by
    have hdiv : R / w ≤ (m : ℝ) - 1 := by rw [hmR]; linarith
    have := (div_le_iff₀ hpos).mp hdiv
    linarith
  have hLm : (m : ℝ) + 3 ≤ (latDist k k0 : ℝ) := by exact_mod_cast hL
  have hgap : R < |y i - x0 i| := by
    rcases (abs_eq hLnn).mp hcentres with hP | hP
    · refine lt_of_lt_of_le ?_ (le_abs_self (y i - x0 i))
      nlinarith [hyi.1, hyi.2, hx0i.1, hx0i.2, hP, hLm, hpos, hRw]
    · refine lt_of_lt_of_le ?_ (neg_le_abs (y i - x0 i))
      nlinarith [hyi.1, hyi.2, hx0i.1, hx0i.2, hP, hLm, hpos, hRw]
  calc R < |y i - x0 i| := hgap
    _ = ‖(y - x0) i‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖y - x0‖ := norm_le_pi_norm _ i

/-- **The exterior cover.**  A point outside `B_r(x0)` lies in a grid cell whose
level is at least the rate attached to `r`. -/
theorem gridDecayRate_le_gridLevel [NeZero d] {n : ℤ} {R r : ℝ} (x0 x : Vec d)
    (hx : x ∉ Metric.ball x0 r) :
    gridDecayRate n R r ≤
      (gridLevel (gridIndex d n x0) (gridSourceRadius n R)
        (gridIndex d n x) : ℝ) := by
  classical
  set w := gridHalfWidth n with hw
  have hpos : 0 < w := gridHalfWidth_pos n
  set k := gridIndex d n x with hkdef
  set k0 := gridIndex d n x0 with hk0
  set m := gridSourceRadius n R with hm
  set j := gridLevel k0 m k with hj
  have hLj : latDist k k0 ≤ m + 3 * j + 2 := latDist_le_of_gridLevel rfl
  have hLjR : (latDist k k0 : ℝ) ≤ (m : ℝ) + 3 * (j : ℝ) + 2 := by exact_mod_cast hLj
  have hkey : r / w - 1 ≤ (latDist k k0 : ℝ) := by
    rcases le_or_gt r 0 with hr | hr
    · have hdiv : r / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg hr hpos.le
      have hnn : (0 : ℝ) ≤ (latDist k k0 : ℝ) := Nat.cast_nonneg _
      linarith
    · have hnot : ¬ ‖x - x0‖ < r := by
        intro hlt
        exact hx (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
      obtain ⟨i, hi⟩ : ∃ i, r ≤ ‖(x - x0) i‖ := by
        by_contra hcon
        push_neg at hcon
        exact hnot ((pi_norm_lt_iff hr).mpr fun i ↦ hcon i)
      have hxi : r ≤ |x i - x0 i| := by simpa [Real.norm_eq_abs] using hi
      have h1 := abs_le.mp (abs_sub_gridCentre_le d n x i)
      have h2 := abs_le.mp (abs_sub_gridCentre_le d n x0 i)
      have hcoordR : (((k i - k0 i).natAbs : ℕ) : ℝ) ≤ (latDist k k0 : ℝ) := by
        exact_mod_cast latDist_coord_le k k0 i
      have hcentres : |(k i : ℝ) * w - (k0 i : ℝ) * w| =
          (((k i - k0 i).natAbs : ℕ) : ℝ) * w := by
        rw [show (k i : ℝ) * w - (k0 i : ℝ) * w = ((k i : ℝ) - (k0 i : ℝ)) * w by ring,
          abs_mul, abs_of_pos hpos, abs_natCast_latDist_coord i]
      have hPle := abs_le.mp (le_of_eq hcentres)
      have hbound : r - w ≤ (((k i - k0 i).natAbs : ℕ) : ℝ) * w := by
        rcases abs_cases (x i - x0 i) with ⟨he, -⟩ | ⟨he, -⟩
        · rw [he] at hxi
          nlinarith [h1.1, h1.2, h2.1, h2.2, hPle.1, hPle.2, hpos]
        · rw [he] at hxi
          nlinarith [h1.1, h1.2, h2.1, h2.2, hPle.1, hPle.2, hpos]
      have hL : r - w ≤ (latDist k k0 : ℝ) * w := by nlinarith [hpos, hcoordR]
      rw [sub_le_iff_le_add, div_le_iff₀ hpos]
      nlinarith [hpos, hL]
  rw [gridDecayRate, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  have hmcast : ((gridSourceRadius n R : ℕ) : ℝ) = (m : ℝ) := by rw [hm]
  rw [hmcast]
  linarith [hkey, hLjR]

/-! ### The exterior row for a globally bounded coefficient -/

private theorem mem_iUnion_of_level_le {count : ℕ → ℕ}
    {cell : (j : ℕ) → Fin (count j) → Set (Vec d)} {rr : ℕ} {x : Vec d} {j : ℕ}
    (hj : rr ≤ j) (i : Fin (count j)) (hx : x ∈ cell j i) :
    x ∈ ⋃ p : Σ k : ℕ, Fin (count (rr + k)), cell (rr + p.1) p.2 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact Set.mem_iUnion.mpr ⟨⟨s, i⟩, hx⟩



theorem wholeSpaceSolution_exterior_decay_of_uniform_smallness [NeZero d]
    {a f : Vec d → ℝ} {t : ℝ} (ht : 0 < t) (haNonneg : ∀ x, 0 ≤ a x)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    {lam Lam : ℝ} (hLam : 0 ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (Set.univ : Set (Vec d))
      (scalarCoeffField a))
    (haLe : ∀ x, a x ≤ Lam)
    {x0 : Vec d} {R : ℝ}
    (hsupp : Function.support f ⊆ Metric.ball x0 R)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∫ x, u.toFun x ^ 2 ∂volume ≤ A)
    {n : ℤ} {theta0 : ℝ} (htheta0 : 0 < theta0)
    (hsmall : 4096 * (d : ℝ) * Lam * t * ((3 : ℝ) ^ n)⁻¹ ^ 2 ≤ theta0)
    (heff : ((2 ^ d : ℕ) : ℝ) * (((7 ^ d : ℕ) : ℝ) * theta0) < 1)
    (r : ℝ) :
    ∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume ≤
      (((2 * gridSourceRadius n R + 5) ^ d : ℕ) : ℝ) * A *
        (1 - ((2 ^ d : ℕ) : ℝ) * (((7 ^ d : ℕ) : ℝ) * theta0))⁻¹ *
        Real.exp (Real.log (((2 ^ d : ℕ) : ℝ) *
          (((7 ^ d : ℕ) : ℝ) * theta0)) * gridDecayRate n R r) := by
  classical
  set k0 := gridIndex d n x0 with hk0
  set m := gridSourceRadius n R with hm
  set count : ℕ → ℕ := fun j ↦ (gridLevelSet k0 m j).card with hcount
  refine wholeSpaceSolution_exterior_decay_of_stopping_cells ht haNonneg u
    (count := count) (fun _ _ ↦ n)
    (fun j i ↦ gridCentre d n (gridCellIndex k0 m j i))
    (fun _ _ ↦ lam) (fun _ _ ↦ Lam)
    ((Metric.ball x0 r)ᶜ) ((2 * m + 5) ^ d) (2 ^ d) (7 ^ d)
    hA0 htheta0 (Nat.pow_pos (by norm_num))
    (Nat.pow_pos (by norm_num)) heff ?_ (fun _ _ ↦ hLam) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- source mass
    intro i
    refine le_trans (setIntegral_le_integral u.memL2_toFun.integrable_sq ?_) hA
    exact Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  · -- ellipticity on each enlargement
    intro j i _
    exact hEll.mono
      (isOpenBoundedConvexDomain_translatedCube d (n + 1)
        (gridCentre d n (gridCellIndex k0 m j i))).isOpen.measurableSet
      (Set.subset_univ _)
  · -- upper bound on each enlargement
    intro j i _ x _
    exact haLe x
  · -- the datum vanishes off the source
    intro j i hj y hy
    have hlev : 0 < gridLevel k0 m (gridCellIndex k0 m j i) := by
      rw [gridLevel_gridCellIndex]
      exact hj
    have hsep : R < ‖y - x0‖ :=
      lt_norm_sub_of_gridLevel_pos x0 hlev hy
    by_contra hfy
    have : y ∈ Metric.ball x0 R := hsupp hfy
    rw [Metric.mem_ball, dist_eq_norm] at this
    linarith
  · -- the smallness condition
    intro _ _ _
    exact hsmall
  · -- the neighbour cover
    intro j i hj
    set k := gridCellIndex k0 m j i with hk
    refine ⟨(gridNeighbours d k).image
      (fun k' ↦ (⟨gridLevel k0 m k', gridFinIndex k0 m k'⟩ :
        Σ l : ℕ, Fin (count l))), ?_, ?_, ?_, ?_⟩
    · exact (Finset.image_nonempty).mpr ⟨k, self_mem_gridNeighbours d k⟩
    · exact Finset.card_image_le.trans (le_of_eq (card_gridNeighbours d k))
    · intro p hp
      obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hp
      have := gridLevel_le_succ_of_mem_gridNeighbours (k0 := k0) (m := m) hk'
      rw [gridLevel_gridCellIndex] at this
      exact this
    · intro y hy
      obtain ⟨k', hk', hy'⟩ :=
        Set.mem_iUnion₂.mp (translatedCube_succ_subset_gridNeighbours d n k hy)
      refine Set.mem_iUnion₂.mpr ⟨_, Finset.mem_image_of_mem _ hk', ?_⟩
      show y ∈ translatedCube d n
        (gridCentre d n (gridCellIndex k0 m (gridLevel k0 m k')
          (gridFinIndex k0 m k')))
      rwa [gridCellIndex_gridFinIndex]
  · -- the sphere count
    intro j
    exact card_gridLevelSet_le_geometric k0 (by rw [hm, gridSourceRadius]; omega) j
  · -- the exterior cover
    intro x hx
    refine mem_iUnion_of_level_le (count := count) ?_
      (gridFinIndex k0 m (gridIndex d n x)) ?_
    · refine Nat.ceil_le.mpr ?_
      exact gridDecayRate_le_gridLevel x0 x hx
    · show x ∈ translatedCube d n
        (gridCentre d n (gridCellIndex k0 m (gridLevel k0 m (gridIndex d n x))
          (gridFinIndex k0 m (gridIndex d n x))))
      rw [gridCellIndex_gridFinIndex]
      exact mem_translatedCube_gridIndex d n x

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
