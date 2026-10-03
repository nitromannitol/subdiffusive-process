module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularArith
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseRosenthal
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridStabilitySubadditivity
public import Homogenization.Deterministic.CoarsePoincare.Setup.Conversions

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## Grid geometry of the triadic annuli -/

/-- A triadic cube whose centre lies in the open cube of its own scale is the
centered cube of that scale. -/
theorem eq_originCube_of_triadicCubeShift_mem_cube {R : TriadicCube d}
    (h : Homogenization.triadicCubeShift R ∈ cube d R.scale) :
    R = Homogenization.originCube d R.scale := by
  have hf : (0 : ℝ) < (3 : ℝ) ^ R.scale := zpow_pos (by norm_num) _
  have h' := (Homogenization.mem_openCubeSet_originCube_iff (d := d)
    (m := R.scale) (x := Homogenization.triadicCubeShift R)).1 h
  have hidx : ∀ i, R.index i = 0 := by
    intro i
    have hi := h' i
    simp only [Homogenization.triadicCubeShift,
      Homogenization.cubeScaleFactor] at hi
    have hlt : (R.index i : ℝ) < 1 / 2 :=
      lt_of_mul_lt_mul_right hi.2 hf.le
    have hgt : (-(1 / 2) : ℝ) < (R.index i : ℝ) :=
      lt_of_mul_lt_mul_right hi.1 hf.le
    have habs : |(R.index i : ℝ)| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    exact_mod_cast Int.abs_lt_one_iff.1 (by exact_mod_cast habs)
  cases R with
  | mk scale index =>
      simp only [Homogenization.originCube]
      congr 1
      exact funext fun i => hidx i

/-- Every point of `□_m` outside `□_n` lies in exactly one triadic annulus
`□_j ∖ □_{j-1}` with `n + 1 ≤ j ≤ m`; this produces one such `j`. -/
theorem exists_annulus_scale_of_mem_cube {n m : ℤ} {z : Vec d}
    (hnm : n ≤ m) (hz : z ∈ cube d m) (hz' : z ∉ cube d n) :
    ∃ j : ℤ, n + 1 ≤ j ∧ j ≤ m ∧ z ∈ cube d j \ cube d (j - 1) := by
  have hex : ∃ i : ℕ, z ∈ cube d (n + (i : ℤ)) := by
    refine ⟨(m - n).toNat, ?_⟩
    have : n + ((m - n).toNat : ℤ) = m := by omega
    rwa [this]
  classical
  set i₀ := Nat.find hex with hi₀
  have hmem : z ∈ cube d (n + (i₀ : ℤ)) := Nat.find_spec hex
  have hpos : i₀ ≠ 0 := by
    intro h
    apply hz'
    have : z ∈ cube d (n + ((0 : ℕ) : ℤ)) := by rw [← h]; exact hmem
    simpa using! this
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : ℕ, i₀ = i₁ + 1 := ⟨i₀ - 1, by omega⟩
  have hnot : z ∉ cube d (n + (i₁ : ℤ)) := by
    have := Nat.find_min hex (m := i₁) (by omega)
    exact this
  have hle : i₀ ≤ (m - n).toNat := by
    refine Nat.find_le ?_
    have : n + ((m - n).toNat : ℤ) = m := by omega
    rwa [this]
  refine ⟨n + (i₀ : ℤ), by omega, by omega, ⟨hmem, ?_⟩⟩
  have : n + (i₀ : ℤ) - 1 = n + (i₁ : ℤ) := by omega
  rw [this]
  exact hnot

/-! ## The annular index set and the annular supremum -/

/-- The annular index set of `e.mathcalE.annular.decomp.pre`: a triadic cube `R`
of scale at most `j - 1`, together with the scale `j ≤ m` of the annulus
`□_j ∖ □_{j-1}` containing the centre of `R`. -/
def AnnularPair (d : ℕ) (m : ℤ) : Set (TriadicCube d × ℤ) :=
  {p | p.2 ≤ m ∧ p.1.scale ≤ p.2 - 1 ∧
    Homogenization.triadicCubeShift p.1 ∈ cube d p.2 \ cube d (p.2 - 1)}

/-- The right side of `e.mathcalE.annular.decomp.pre`: the supremum of the
`3^{-(3/2)s(m-n)}`-discounted observables over the annular index set. -/
def annularSup (s : ℝ) (m : ℤ) (g : TriadicCube d → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ p : AnnularPair d m,
    ENNReal.ofReal
        ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - ((p.1.1.scale : ℤ) : ℝ)))) *
      g p.1.1

/-- The maximum of `g` over the scale-`k` cubes whose centre lies in the
annulus `□_{k+1} ∖ □_k`.  This is the manuscript's
`max_{z ∈ 3^k ℤ^d ∩ (□_{k+1} ∖ □_k)} J(z + □_k)`. -/
def annulusMax (g : TriadicCube d → ℝ≥0∞) (k : ℤ) : ℝ≥0∞ :=
  ⨆ R : {R : TriadicCube d // R.scale = k ∧
      Homogenization.triadicCubeShift R ∈ cube d (k + 1) \ cube d k}, g R.1

/-- Every annulus maximum at a scale `k ≤ m - 1` is dominated by the annular
supremum, at the cost of the discount factor. -/
theorem annulusMax_le_annularSup {s : ℝ} {m k : ℤ} (hk : k ≤ m - 1)
    (g : TriadicCube d → ℝ≥0∞) :
    annulusMax g k ≤
      ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((m : ℝ) - (k : ℝ)))) *
        annularSup s m g := by
  refine iSup_le fun R => ?_
  obtain ⟨hscale, hann⟩ := R.2
  have hk1 : k + 1 - 1 = k := by ring
  have hmem : (R.1, k + 1) ∈ AnnularPair d m := by
    refine ⟨by omega, ?_, ?_⟩
    · show R.1.scale ≤ k + 1 - 1
      omega
    · show Homogenization.triadicCubeShift R.1 ∈
        cube d (k + 1) \ cube d (k + 1 - 1)
      rw [hk1]
      exact hann
  have hle : ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (k : ℝ)))) *
      g R.1 ≤ annularSup s m g := by
    have := le_iSup (fun p : AnnularPair d m =>
      ENNReal.ofReal
          ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - ((p.1.1.scale : ℤ) : ℝ)))) *
        g p.1.1) ⟨(R.1, k + 1), hmem⟩
    simpa [annularSup, hscale] using! this
  calc g R.1
      = ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((m : ℝ) - (k : ℝ)))) *
          (ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (k : ℝ)))) *
            g R.1) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
          ← Real.rpow_add (by norm_num)]
        norm_num
    _ ≤ _ := by gcongr

/-- Any member of the annular index set is dominated by the annular supremum,
at the cost of the discount factor at its own scale. -/
theorem le_mul_annularSup_of_annularPair {s : ℝ} {m j : ℤ} {R : TriadicCube d}
    (g : TriadicCube d → ℝ≥0∞) (h : (R, j) ∈ AnnularPair d m) :
    g R ≤
      ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((m : ℝ) - (R.scale : ℝ)))) *
        annularSup s m g := by
  have hle : ENNReal.ofReal
        ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ)))) * g R ≤
      annularSup s m g := by
    have := le_iSup (fun p : AnnularPair d m =>
      ENNReal.ofReal
          ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - ((p.1.1.scale : ℤ) : ℝ)))) *
        g p.1.1) ⟨(R, j), h⟩
    simpa [annularSup] using! this
  calc g R
      = ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2 * ((m : ℝ) - (R.scale : ℝ)))) *
          (ENNReal.ofReal
              ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ)))) * g R) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
          ← Real.rpow_add (by norm_num)]
        norm_num
    _ ≤ _ := by gcongr

/-! ## The central cube is a descendant -/

/-- A triadic cube containing the origin in its half-open realization is the
centered cube of its scale. -/
theorem eq_originCube_of_zero_mem_cubeSet {R : TriadicCube d}
    (h : (0 : Vec d) ∈ Homogenization.cubeSet R) :
    R = Homogenization.originCube d R.scale := by
  have hf : (0 : ℝ) < (3 : ℝ) ^ R.scale := zpow_pos (by norm_num) _
  have hidx : ∀ i, R.index i = 0 := by
    intro i
    have hi := h i
    simp only [Homogenization.cubeScaleFactor] at hi
    have h1 : ((R.index i : ℝ) - 1 / 2) * (3 : ℝ) ^ R.scale ≤
        0 * (3 : ℝ) ^ R.scale := by
      simpa using! hi.1
    have h2 : (0 : ℝ) * (3 : ℝ) ^ R.scale <
        ((R.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ R.scale := by
      simpa using! hi.2
    have hle : (R.index i : ℝ) - 1 / 2 ≤ 0 := le_of_mul_le_mul_right h1 hf
    have hgt : (0 : ℝ) < (R.index i : ℝ) + 1 / 2 :=
      lt_of_mul_lt_mul_right h2 hf.le
    have habs : |(R.index i : ℝ)| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    exact_mod_cast Int.abs_lt_one_iff.1 (by exact_mod_cast habs)
  cases R with
  | mk scale index =>
      simp only [Homogenization.originCube]
      congr 1
      exact funext fun i => hidx i

/-- The centered cube of scale `n ≤ m` is a scale-`n` descendant of `□_m`. -/
theorem originCube_mem_descendantsAtScale {n m : ℤ} (hnm : n ≤ m) :
    Homogenization.originCube d n ∈
      Homogenization.descendantsAtScale (Homogenization.originCube d m) n := by
  have hf : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  have h0 : (0 : Vec d) ∈
      Homogenization.cubeSet (Homogenization.originCube d m) := by
    refine Homogenization.mem_cubeSet_originCube_iff.2 fun i => ?_
    constructor <;> simp <;> linarith
  have hsub := Homogenization.cubeSet_subset_iUnion_descendantsAtScale
    (Homogenization.originCube d m) (k := n) (by simpa only [Homogenization.originCube] using! hnm) h0
  obtain ⟨R, hR2⟩ := Set.mem_iUnion.1 hsub
  obtain ⟨hR, hxR⟩ := Set.mem_iUnion.1 hR2
  have hscale : R.scale = n :=
    Homogenization.scale_eq_of_mem_descendantsAtScale hR
  have hReq : R = Homogenization.originCube d n := by
    have := eq_originCube_of_zero_mem_cubeSet hxR
    rwa [hscale] at this
  rwa [hReq] at hR

/-! ## The annular decomposition -/

/-- **The annular decomposition, `e.mathcalE.annular.decomp.pre`.**

The discounted `ℓ²`-in-scales series of the scale-`n` grid maxima over `□_m`
is at most `64` times the annular supremum, provided the value of the *centered*
cube at each scale is charged to the annuli by the manuscript's countable
subadditivity (`hcentral`).

`hcentral` is the only input: it is the Lean form of the manuscript's
`J(□_n) ≤ ∑_{k<n} 3^{-d(n-1-k)} max_{z ∈ 3^kℤ^d ∩ (□_{k+1} ∖ □_k)} J(z + □_k)`,
which follows from countable subadditivity of the response over the triadic
onion of `□_n`.  Everything else — the annular cover of the grid, the split of
the descendant maximum, the two geometric resummations, and the trade of the
`3^{-2s(m-n)}` series weight for the `3^{-(3/2)s(m-n)}` supremum weight — is
proved here. -/
theorem tsum_geometricWeight_descendantSup_le_annularSup
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (hd : 1 ≤ d) (m : ℕ)
    (g : TriadicCube d → ℝ≥0∞)
    (hcentral : ∀ n : ℤ, n ≤ (m : ℤ) →
      g (Homogenization.originCube d n) ≤
        ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * (t : ℝ))) *
          annulusMax g (n - 1 - (t : ℤ))) :
    ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
        (⨆ R : {R : TriadicCube d // R ∈ Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))}, g R.1) ≤
      64 * annularSup s (m : ℤ) g := by
  classical
  set K : ℝ≥0∞ := annularSup s (m : ℤ) g with hK
  refine tsum_geometricWeight_le_of_annular_split (D := (d : ℝ)) hs hs2
    (by exact_mod_cast hd)
    (Ann := fun l => ⨆ R : {R : TriadicCube d //
        R ∈ Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ)) ∧
          Homogenization.triadicCubeShift R ∉ cube d ((m : ℤ) - (l : ℤ))},
      g R.1)
    (Cen := fun l => g (Homogenization.originCube d ((m : ℤ) - (l : ℤ))))
    (Y := fun l t => annulusMax g ((m : ℤ) - (l : ℤ) - 1 - (t : ℤ)))
    ?_ ?_ ?_ ?_
  · -- the grid maximum splits into an annular part and the centre
    intro l
    refine iSup_le fun R => ?_
    have hscale : R.1.scale = (m : ℤ) - (l : ℤ) :=
      Homogenization.scale_eq_of_mem_descendantsAtScale R.2
    by_cases hc : Homogenization.triadicCubeShift R.1 ∈ cube d ((m : ℤ) - (l : ℤ))
    · have hReq : R.1 = Homogenization.originCube d ((m : ℤ) - (l : ℤ)) := by
        have := eq_originCube_of_triadicCubeShift_mem_cube (R := R.1)
          (by rw [hscale]; exact hc)
        rwa [hscale] at this
      rw [hReq]
      exact le_add_self
    · refine le_trans ?_ le_self_add
      exact le_iSup (fun R' : {R' : TriadicCube d //
        R' ∈ Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ)) ∧
          Homogenization.triadicCubeShift R' ∉ cube d ((m : ℤ) - (l : ℤ))} =>
        g R'.1) ⟨R.1, R.2, hc⟩
  · -- the annular part
    intro l
    refine iSup_le fun R => ?_
    obtain ⟨hRmem, hRnot⟩ := R.2
    have hscale : R.1.scale = (m : ℤ) - (l : ℤ) :=
      Homogenization.scale_eq_of_mem_descendantsAtScale hRmem
    have hle : ((m : ℤ) - (l : ℤ)) ≤ (m : ℤ) := by omega
    have hin : Homogenization.triadicCubeShift R.1 ∈ cube d (m : ℤ) :=
      triadicCubeShift_mem_cube_of_mem_descendantsAtScale hle hRmem
    obtain ⟨j, hj1, hj2, hj3⟩ := exists_annulus_scale_of_mem_cube hle hin hRnot
    have hmem : (R.1, j) ∈ AnnularPair d (m : ℤ) := by
      refine ⟨hj2, ?_, hj3⟩
      show R.1.scale ≤ j - 1
      omega
    have hcast : ((m : ℤ) : ℝ) - ((R.1.scale : ℤ) : ℝ) = (l : ℝ) := by
      rw [hscale]
      push_cast
      ring
    have := le_mul_annularSup_of_annularPair (s := s) g hmem
    rwa [hcast] at this
  · -- the centre, by the countable subadditivity input
    intro l
    exact hcentral ((m : ℤ) - (l : ℤ)) (by omega)
  · -- the annuli feeding the centre
    intro l t
    have hk : (m : ℤ) - (l : ℤ) - 1 - (t : ℤ) ≤ (m : ℤ) - 1 := by omega
    have hcast : ((m : ℤ) : ℝ) -
        (((m : ℤ) - (l : ℤ) - 1 - (t : ℤ) : ℤ) : ℝ) =
          (l : ℝ) + 1 + (t : ℝ) := by push_cast; ring
    have := annulusMax_le_annularSup (s := s) hk g
    rwa [hcast] at this

/-! ## The one-scale refinement `j - 1 → j - 2` -/

private theorem three_zpow_sub_one (j : ℤ) :
    (3 : ℝ) ^ (j - 1) = 3 * (3 : ℝ) ^ (j - 2) := by
  rw [show j - 1 = (j - 2) + 1 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  ring

private theorem three_zpow_self (j : ℤ) :
    (3 : ℝ) ^ j = 9 * (3 : ℝ) ^ (j - 2) := by
  rw [show j = (j - 2) + 2 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  norm_num
  ring

/-- Every child of a scale-`j-1` cube whose centre lies in the annulus
`□_j ∖ □_{j-1}` again has its centre in that annulus, one scale down.

The centres of the children of `R` sit at distance at most `3^{j-2}` from the
centre of `R`, which is enough to stay inside `□_j` and outside `□_{j-1}`. -/
theorem childCube_shift_mem_annulus {R R' : TriadicCube d} {j : ℤ}
    (hscale : R.scale = j - 1)
    (hann : Homogenization.triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    (hR' : R' ∈ Homogenization.childCubes R) :
    R'.scale = j - 2 ∧
      Homogenization.triadicCubeShift R' ∈ cube d j \ cube d (j - 1) := by
  classical
  obtain ⟨digits, rfl⟩ := Homogenization.mem_childCubes_iff.1 hR'
  have hfpos : (0 : ℝ) < (3 : ℝ) ^ (j - 2) := zpow_pos (by norm_num) _
  have h3 : (3 : ℝ) ^ (j - 1) = 3 * (3 : ℝ) ^ (j - 2) := three_zpow_sub_one j
  have h9 : (3 : ℝ) ^ j = 9 * (3 : ℝ) ^ (j - 2) := three_zpow_self j
  have hjj : j - 1 - 1 = j - 2 := by ring
  have hdig : ∀ i, 0 ≤ ((digits i : ℕ) : ℤ) ∧ ((digits i : ℕ) : ℤ) ≤ 2 := by
    intro i
    have := (digits i).isLt
    omega
  -- every coordinate index of `R` is `-1`, `0` or `1`
  have hidx : ∀ i, R.index i = -1 ∨ R.index i = 0 ∨ R.index i = 1 := by
    intro i
    have hi := Homogenization.mem_openCubeSet_originCube_iff.1 hann.1 i
    simp only [Homogenization.triadicCubeShift, Homogenization.cubeScaleFactor,
      hscale, h3, h9] at hi
    have hlt : (R.index i : ℝ) < 2 := by nlinarith [hi.2]
    have hgt : (-2 : ℝ) < (R.index i : ℝ) := by nlinarith [hi.1]
    have hlt' : R.index i < 2 := by exact_mod_cast hlt
    have hgt' : (-2 : ℤ) < R.index i := by exact_mod_cast hgt
    omega
  -- some coordinate index of `R` is `±1`
  have hout : ∃ i, R.index i = -1 ∨ R.index i = 1 := by
    by_contra hcon
    push_neg at hcon
    refine hann.2 (Homogenization.mem_openCubeSet_originCube_iff.2 fun i => ?_)
    have hz : R.index i = 0 := by
      rcases hidx i with h | h | h
      · exact absurd h (hcon i).1
      · exact h
      · exact absurd h (hcon i).2
    simp only [Homogenization.triadicCubeShift, Homogenization.cubeScaleFactor,
      hscale, hz, h3]
    constructor <;> [nlinarith; nlinarith]
  refine ⟨by show R.scale - 1 = j - 2; omega, ?_, ?_⟩
  · -- inside `□_j`
    refine Homogenization.mem_openCubeSet_originCube_iff.2 fun i => ?_
    have hd := hdig i
    have hi3 := hidx i
    have hup : 3 * R.index i + ((digits i : ℕ) : ℤ) - 1 ≤ 4 := by
      rcases hi3 with h | h | h <;> omega
    have hlo : (-4 : ℤ) ≤ 3 * R.index i + ((digits i : ℕ) : ℤ) - 1 := by
      rcases hi3 with h | h | h <;> omega
    have hupr : ((3 * R.index i + ((digits i : ℕ) : ℤ) - 1 : ℤ) : ℝ) ≤ 4 := by
      exact_mod_cast hup
    have hlor : (-4 : ℝ) ≤ ((3 * R.index i + ((digits i : ℕ) : ℤ) - 1 : ℤ) : ℝ) := by
      exact_mod_cast hlo
    simp only [Homogenization.triadicCubeShift, Homogenization.cubeScaleFactor,
      hscale, hjj, h9]
    push_cast at hupr hlor ⊢
    constructor <;> nlinarith
  · -- outside `□_{j-1}`
    obtain ⟨i, hi⟩ := hout
    intro hmem
    have hmi := Homogenization.mem_openCubeSet_originCube_iff.1 hmem i
    have hd := hdig i
    simp only [Homogenization.triadicCubeShift, Homogenization.cubeScaleFactor,
      hscale, hjj, h3] at hmi
    rcases hi with h | h
    · have hX : 3 * R.index i + ((digits i : ℕ) : ℤ) - 1 ≤ -2 := by omega
      have hXr : ((3 * R.index i + ((digits i : ℕ) : ℤ) - 1 : ℤ) : ℝ) ≤ -2 := by
        exact_mod_cast hX
      push_cast at hXr hmi
      nlinarith [hmi.1]
    · have hX : (2 : ℤ) ≤ 3 * R.index i + ((digits i : ℕ) : ℤ) - 1 := by omega
      have hXr : (2 : ℝ) ≤ ((3 * R.index i + ((digits i : ℕ) : ℤ) - 1 : ℤ) : ℝ) := by
        exact_mod_cast hX
      push_cast at hXr hmi
      nlinarith [hmi.2]

/-- The refined annular index set of the frozen target: the cube scale is at
most `j - 2`. -/
def AnnularPairTwo (d : ℕ) (m : ℤ) : Set (TriadicCube d × ℤ) :=
  {p | p.2 ≤ m ∧ p.1.scale ≤ p.2 - 2 ∧
    Homogenization.triadicCubeShift p.1 ∈ cube d p.2 \ cube d (p.2 - 1)}

/-- The refined annular supremum, over `AnnularPairTwo`. -/
def annularSupTwo (s : ℝ) (m : ℤ) (g : TriadicCube d → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ p : AnnularPairTwo d m,
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (p.1.1.scale : ℝ)))) *
      g p.1.1

/-- **The one-scale refinement.**

If every cube's observable is dominated by that of one of its children — the
manuscript's one-step subadditivity
`J(z + □_{j-1}) ≤ max_{z' ∈ 3^{j-2}ℤ^d ∩ (z + □_{j-1})} J(z' + □_{j-2})` — then
the annular supremum at `n ≤ j - 1` is at most three times the refined annular
supremum at `n ≤ j - 2`, which is the index range of the frozen target. -/
theorem annularSup_le_three_mul_annularSupTwo {s : ℝ} (hs2 : s ≤ 1 / 2) {m : ℤ} (g : TriadicCube d → ℝ≥0∞)
    (hchild : ∀ R : TriadicCube d,
      ∃ R' ∈ Homogenization.childCubes R, g R ≤ g R') :
    annularSup s m g ≤ 3 * annularSupTwo s m g := by
  have h3 : ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) ≤ 3 := by
    have hle : (3 : ℝ) ^ (3 * s / 2) ≤ 3 := by
      calc (3 : ℝ) ^ (3 * s / 2) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 3 := Real.rpow_one 3
    simpa using! ENNReal.ofReal_le_ofReal hle
  refine iSup_le fun p => ?_
  obtain ⟨hj, hsc, hann⟩ := p.2
  rcases lt_or_eq_of_le hsc with hlt | heq
  · -- already refined
    have hmem : (p.1.1, p.1.2) ∈ AnnularPairTwo d m := by
      refine ⟨hj, ?_, hann⟩
      show p.1.1.scale ≤ p.1.2 - 2
      omega
    have hle := le_iSup (fun q : AnnularPairTwo d m =>
      ENNReal.ofReal
          ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (q.1.1.scale : ℝ)))) * g q.1.1)
      ⟨(p.1.1, p.1.2), hmem⟩
    refine le_trans ?_ (le_trans hle (le_mul_of_one_le_left (zero_le) ?_))
    · exact le_of_eq rfl
    · norm_num
  · -- refine by passing to a child
    obtain ⟨R', hR'mem, hR'le⟩ := hchild p.1.1
    obtain ⟨hR'scale, hR'ann⟩ :=
      childCube_shift_mem_annulus (j := p.1.2) heq hann hR'mem
    have hmem : (R', p.1.2) ∈ AnnularPairTwo d m := by
      refine ⟨hj, ?_, hR'ann⟩
      show R'.scale ≤ p.1.2 - 2
      omega
    have hle := le_iSup (fun q : AnnularPairTwo d m =>
      ENNReal.ofReal
          ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (q.1.1.scale : ℝ)))) * g q.1.1)
      ⟨(R', p.1.2), hmem⟩
    have hcast : ((m : ℝ) - (p.1.1.scale : ℝ)) =
        ((m : ℝ) - (R'.scale : ℝ)) - 1 := by
      rw [heq, hR'scale]
      push_cast
      ring
    calc ENNReal.ofReal
          ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (p.1.1.scale : ℝ)))) * g p.1.1
        ≤ ENNReal.ofReal
            ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (p.1.1.scale : ℝ)))) * g R' := by
          gcongr
      _ = ENNReal.ofReal ((3 : ℝ) ^ (3 * s / 2)) *
            (ENNReal.ofReal
              ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R'.scale : ℝ)))) * g R') := by
          have he : -(3 * s / 2) * (((m : ℝ) - (R'.scale : ℝ)) - 1) =
              3 * s / 2 + -(3 * s / 2) * ((m : ℝ) - (R'.scale : ℝ)) := by ring
          rw [hcast, ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
            ← Real.rpow_add (by norm_num), he]
      _ ≤ 3 * annularSupTwo s m g := by
          refine mul_le_mul' h3 ?_
          exact hle

/-! ## The frozen carrier in annular form -/

/-- The local observable of the annular decomposition: the unit-sphere maximum
of the paper probe on the centered cube of the scale of `R`, at the sample
translated to the centre of `R`.

This is `max_{|e| = 1} J(z + □_n, e, e; ã_{L,m})` at `z = triadicCubeShift R`,
`n = R.scale`, carrying the *global* cutoff `L` and the *global* normalization
`alpha`.  Converting it to the frozen `section6Response M n n ω z e` atoms
(local cutoff `n`, normalization `ahom_n`) is the separate
coefficient-sensitivity step. -/
def section6LocalProbeMax (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) (alpha : ℝ)
    (R : TriadicCube d) : ℝ≥0∞ :=
  ⨆ e : {e : Vec d // Homogenization.vecNormSq e = 1},
    ENNReal.ofReal
      (paperScalarProbe (Homogenization.originCube d R.scale)
        (aCutoffFamily M L
          (translatePotentialSample (Homogenization.triadicCubeShift R)
            (translatePotentialSample z ω)))
        alpha e)

/-- **The section 6 error carrier in annular form.**

The frozen `q = 2` error at `□_m` is bounded by the square root of `64` times
the annular supremum of the local probes over the triadic annuli
`□_j ∖ □_{j-1}`, `R.scale ≤ j - 1`, `j ≤ m`.

This conditional helper isolates the countable-subadditivity input.  It is
discharged below by `section6LocalProbeMax_originCube_le_onion`. -/
theorem section6HomogenizationError_le_annularSup_of_countableSubadditivity
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (hd : 1 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hcentral : ∀ n : ℤ, n ≤ (m : ℤ) →
      section6LocalProbeMax M L ω z
          (tailCoefficientCubeAverage M L m (translatePotentialSample z ω))
          (Homogenization.originCube d n) ≤
        ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * (t : ℝ))) *
          annulusMax
            (section6LocalProbeMax M L ω z
              (tailCoefficientCubeAverage M L m (translatePotentialSample z ω)))
            (n - 1 - (t : ℤ))) :
    ENNReal.ofReal (section6HomogenizationError M s L m ω z) ≤
      (64 * annularSup s (m : ℤ)
          (section6LocalProbeMax M L ω z
            (tailCoefficientCubeAverage M L m
              (translatePotentialSample z ω)))) ^ (1 / 2 : ℝ) := by
  set alpha : ℝ :=
    tailCoefficientCubeAverage M L m (translatePotentialSample z ω) with halpha
  set g : TriadicCube d → ℝ≥0∞ := section6LocalProbeMax M L ω z alpha with hg
  have hseries : ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
      (⨆ R : {R : TriadicCube d // R ∈ Homogenization.descendantsAtScale
          (Homogenization.originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))}, g R.1) ≤
      64 * annularSup s (m : ℤ) g :=
    tsum_geometricWeight_descendantSup_le_annularSup hs hs2 hd m g hcentral
  have hrw : section6HomogenizationError M s L m ω z =
      ((∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
        (⨆ R : {R : TriadicCube d // R ∈ Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))},
          g R.1)) ^ (1 / 2 : ℝ)).toReal := by
    rw [section6HomogenizationError_eq_transported_series]
    congr 2
    refine tsum_congr fun l => ?_
    congr 1
    refine iSup_congr fun R => ?_
    rw [hg, section6LocalProbeMax,
      Homogenization.scale_eq_of_mem_descendantsAtScale R.2]
  rw [hrw]
  refine le_trans ENNReal.ofReal_toReal_le ?_
  exact ENNReal.rpow_le_rpow hseries (by norm_num)

/-- **The section 6 error carrier in the refined annular form.**

The same bound as the conditional annular endpoint, but over the
refined index range `R.scale ≤ j - 2` of the frozen target, obtained from the
one-scale subadditivity input `hchild`.

This conditional helper is discharged below.  What remains between the final
unconditional endpoint and the
frozen right side is: the sub-unit tail (the scales `R.scale < 0`, which the
manuscript charges to the `C s⁻¹ δ²` term), the identification of
`triadicCubeShift R` with an `OnTriadicGrid` point (supplied by
`onTriadicGrid_triadicCubeShift_of_scale`), the passage from
`3^{-(3/4)s(m-n)}` to the frozen `3^{-(s/2)(m-n)}` after the square root, and
the coefficient-sensitivity step converting the global-cutoff probes
`section6LocalProbeMax M L ω z alpha` into the frozen atoms
`section6Response M n n ω z e`. -/
theorem section6HomogenizationError_le_annularSupTwo_of_subadditivity
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (hd : 1 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hcentral : ∀ n : ℤ, n ≤ (m : ℤ) →
      section6LocalProbeMax M L ω z
          (tailCoefficientCubeAverage M L m (translatePotentialSample z ω))
          (Homogenization.originCube d n) ≤
        ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * (t : ℝ))) *
          annulusMax
            (section6LocalProbeMax M L ω z
              (tailCoefficientCubeAverage M L m (translatePotentialSample z ω)))
            (n - 1 - (t : ℤ)))
    (hchild : ∀ R : TriadicCube d, ∃ R' ∈ Homogenization.childCubes R,
      section6LocalProbeMax M L ω z
          (tailCoefficientCubeAverage M L m (translatePotentialSample z ω)) R ≤
        section6LocalProbeMax M L ω z
          (tailCoefficientCubeAverage M L m (translatePotentialSample z ω)) R') :
    ENNReal.ofReal (section6HomogenizationError M s L m ω z) ≤
      (192 * annularSupTwo s (m : ℤ)
          (section6LocalProbeMax M L ω z
            (tailCoefficientCubeAverage M L m
              (translatePotentialSample z ω)))) ^ (1 / 2 : ℝ) := by
  refine le_trans
    (section6HomogenizationError_le_annularSup_of_countableSubadditivity
      hs hs2 hd M L m ω z hcentral) ?_
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  calc (64 : ℝ≥0∞) * annularSup s (m : ℤ) _
      ≤ 64 * (3 * annularSupTwo s (m : ℤ) _) := by
        gcongr
        exact annularSup_le_three_mul_annularSupTwo hs2 _ hchild
    _ = 192 * annularSupTwo s (m : ℤ) _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

private theorem originCube_pred_mem_childCubes (d : ℕ) (k : ℤ) :
    originCube d (k - 1) ∈ childCubes (originCube d k) := by
  rw [mem_childCubes_iff]
  refine ⟨fun _ => (1 : Fin 3), ?_⟩
  apply congrArg₂ TriadicCube.mk
  · rfl
  · funext i
    simp only [originCube]
    norm_num

private theorem openCubeSet_originCube_mono {k l : ℤ} (hkl : k ≤ l) :
    openCubeSet (originCube d k) ⊆ openCubeSet (originCube d l) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have hpow : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ l :=
    zpow_le_zpow_right₀ (by norm_num) hkl
  exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩

private def OnionCube (d : ℕ) (n : ℤ) (t : ℕ) :=
  {R : TriadicCube d //
    R ∈ childCubes (originCube d (n - (t : ℤ))) ∧
      R ≠ originCube d (n - 1 - (t : ℤ))}

private abbrev OnionIndex (d : ℕ) (n : ℤ) :=
  Σ t : ℕ, OnionCube d n t

private noncomputable instance onionCubeFintype (d : ℕ) (n : ℤ) (t : ℕ) :
    Fintype (OnionCube d n t) :=
  Fintype.ofFinset
    ((childCubes (originCube d (n - (t : ℤ)))).filter
      (fun R => R ≠ originCube d (n - 1 - (t : ℤ))))
    (by
      intro R
      rw [Finset.mem_filter]
      rfl)

private theorem onionCube_scale {n : ℤ} {t : ℕ} (R : OnionCube d n t) :
    R.1.scale = n - 1 - (t : ℤ) := by
  have := child_scale_of_mem_childCubes R.2.1
  change R.1.scale = n - (t : ℤ) - 1 at this
  omega

private theorem triadicCubeShift_mem_openCubeSet (R : TriadicCube d) :
    triadicCubeShift R ∈ openCubeSet R := by
  intro i
  simp only [triadicCubeShift, cubeScaleFactor]
  have hpos : (0 : ℝ) < (3 : ℝ) ^ R.scale := by positivity
  constructor <;> nlinarith

private theorem onionCube_shift_mem_annulus {n : ℤ} {t : ℕ}
    (R : OnionCube d n t) :
    triadicCubeShift R.1 ∈
      cube d (n - (t : ℤ)) \ cube d (n - 1 - (t : ℤ)) := by
  have hcenter := triadicCubeShift_mem_openCubeSet R.1
  have hupper := openCubeSet_subset_of_mem_childCubes R.2.1 hcenter
  refine ⟨hupper, ?_⟩
  intro hinner
  have hcentral : originCube d (n - 1 - (t : ℤ)) ∈
      childCubes (originCube d (n - (t : ℤ))) := by
    rw [show n - 1 - (t : ℤ) = n - (t : ℤ) - 1 by ring]
    exact originCube_pred_mem_childCubes d (n - (t : ℤ))
  have hdisj := disjoint_cubeSet_of_ne_mem_childCubes R.2.1 hcentral R.2.2
  exact Set.disjoint_left.1 hdisj
    (openCubeSet_subset_cubeSet R.1 hcenter)
    (openCubeSet_subset_cubeSet _ hinner)

private theorem onionCells_pairwiseDisjoint (n : ℤ) :
    Pairwise (Function.onFun Disjoint
      (fun p : OnionIndex d n => openCubeSet p.2.1)) := by
  rintro ⟨t, R⟩ ⟨u, S⟩ hne
  rcases lt_trichotomy t u with htu | htu | htu
  · have hcentral : originCube d (n - 1 - (t : ℤ)) ∈
        childCubes (originCube d (n - (t : ℤ))) := by
      rw [show n - 1 - (t : ℤ) = n - (t : ℤ) - 1 by ring]
      exact originCube_pred_mem_childCubes d (n - (t : ℤ))
    have hdisj := disjoint_cubeSet_of_ne_mem_childCubes R.2.1 hcentral R.2.2
    have htuZ : (t : ℤ) < (u : ℤ) := by exact_mod_cast htu
    refine hdisj.mono (openCubeSet_subset_cubeSet R.1) ?_
    refine fun x hx => openCubeSet_subset_cubeSet _
      (openCubeSet_originCube_mono (d := d) (k := n - (u : ℤ))
        (l := n - 1 - (t : ℤ)) (by omega)
        (openCubeSet_subset_of_mem_childCubes S.2.1 hx))
  · subst u
    have hRS : R.1 ≠ S.1 := by
      intro h
      apply hne
      have hRSsub : R = S := Subtype.ext h
      subst S
      rfl
    exact (disjoint_cubeSet_of_ne_mem_childCubes R.2.1 S.2.1 hRS).mono
      (openCubeSet_subset_cubeSet R.1) (openCubeSet_subset_cubeSet S.1)
  · have hcentral : originCube d (n - 1 - (u : ℤ)) ∈
        childCubes (originCube d (n - (u : ℤ))) := by
      rw [show n - 1 - (u : ℤ) = n - (u : ℤ) - 1 by ring]
      exact originCube_pred_mem_childCubes d (n - (u : ℤ))
    have hdisj := disjoint_cubeSet_of_ne_mem_childCubes S.2.1 hcentral S.2.2
    have hutZ : (u : ℤ) < (t : ℤ) := by exact_mod_cast htu
    refine (hdisj.mono (openCubeSet_subset_cubeSet S.1) ?_).symm
    refine fun x hx => openCubeSet_subset_cubeSet _
      (openCubeSet_originCube_mono (d := d) (k := n - (t : ℤ))
        (l := n - 1 - (u : ℤ)) (by omega)
        (openCubeSet_subset_of_mem_childCubes R.2.1 hx))

private theorem exists_not_mem_small_originCube [NeZero d]
    {n : ℤ} {x : Vec d} (hx : x ≠ 0) :
    ∃ N : ℕ, x ∉ openCubeSet (originCube d (n - 1 - (N : ℤ))) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have habs : 0 < |x i| := abs_pos.mpr hi
  have hbase : 0 < (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 1) := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (div_pos habs hbase) (by norm_num : (1 / 3 : ℝ) < 1)
  refine ⟨N, ?_⟩
  intro hmem
  have hiMem := (mem_openCubeSet_originCube_iff.1 hmem) i
  have hpow : (3 : ℝ) ^ (n - 1 - (N : ℤ)) =
      (3 : ℝ) ^ (n - 1) * (1 / 3 : ℝ) ^ N := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast,
      div_eq_mul_inv,
      show ((3 : ℝ) ^ N)⁻¹ = (1 / 3 : ℝ) ^ N by
        rw [← inv_pow]
        norm_num]
  have habsBound : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 1 - (N : ℤ)) := by
    rw [abs_lt]
    exact ⟨by nlinarith [hiMem.1], hiMem.2⟩
  rw [hpow] at habsBound
  have hsmall := mul_lt_mul_of_pos_left hN hbase
  rw [mul_div_cancel₀ _ (ne_of_gt hbase)] at hsmall
  linarith

private theorem volume_onion_diff_iUnion_openCubeSet [NeZero d] (n : ℤ) :
    volume (openCubeSet (originCube d n) \
      ⋃ p : OnionIndex d n, openCubeSet p.2.1) = 0 := by
  have hsub : openCubeSet (originCube d n) \
      (⋃ p : OnionIndex d n, openCubeSet p.2.1) ⊆
        ({0} : Set (Vec d)) ∪ ⋃ R : TriadicCube d, cubeBoundary R := by
    rintro x ⟨hxV, hxnot⟩
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    right
    by_contra hboundary
    have hnotBoundary : ∀ R : TriadicCube d, x ∉ cubeBoundary R := by
      intro R hxR
      exact hboundary (Set.mem_iUnion.2 ⟨R, hxR⟩)
    obtain ⟨N, hsmall⟩ := exists_not_mem_small_originCube (d := d) (n := n) hx0
    obtain ⟨j, hjlow, hjhigh, hxann⟩ :=
      exists_annulus_scale_of_mem_cube
        (n := n - 1 - (N : ℤ)) (m := n) (by omega) hxV hsmall
    obtain ⟨R, hRchild, hxR⟩ :=
      exists_mem_childCubes_of_mem_cubeSet
        (show x ∈ cubeSet (originCube d j) from
          openCubeSet_subset_cubeSet _ hxann.1)
    have hxRopen : x ∈ openCubeSet R := by
      by_contra hnopen
      exact hnotBoundary R (mem_cubeBoundary_iff.2 ⟨hxR, hnopen⟩)
    have hRne : R ≠ originCube d (j - 1) := by
      intro h
      subst R
      exact hxann.2 hxRopen
    let t : ℕ := (n - j).toNat
    have ht : (t : ℤ) = n - j := Int.toNat_of_nonneg (by omega)
    have hparent : originCube d (n - (t : ℤ)) = originCube d j := by
      rw [ht]
      congr 1
      omega
    have hcentral : originCube d (n - 1 - (t : ℤ)) = originCube d (j - 1) := by
      rw [ht]
      congr 1
      omega
    let p : OnionIndex d n :=
      ⟨t, ⟨R, by simpa only [hparent, hcentral] using! And.intro hRchild hRne⟩⟩
    exact hxnot (Set.mem_iUnion.2 ⟨p, hxRopen⟩)
  refine measure_mono_null hsub ?_
  apply measure_union_null
  · simp
  · exact measure_iUnion_null fun R => volume_cubeBoundary_eq_zero R

private theorem exists_isEllipticFieldOn_aCutoff_openCubeSet
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (sample : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      IsEllipticFieldOn lam Lam (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L sample)) := by
  let a0 := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L sample
  have ha : Continuous a0 := SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L sample
  have hcompact : IsCompact (closure (openCubeSet Q)) :=
    (Ch02.cubeDomain Q).isDomain.isBoundedDomain.isBounded.isCompact_closure
  have hnonempty : (closure (openCubeSet Q)).Nonempty :=
    (Ch02.cubeDomain Q).nonempty.closure
  obtain ⟨xmin, hxmin, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty ha.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty ha.continuousOn
  refine ⟨a0 xmin, a0 xmax,
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L sample xmin, ?_⟩
  constructor
  · have hmatrix : Continuous fun x : Vec d => scalarCoeffField a0 x :=
      ha.smul continuous_const
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    have hentry : Measurable fun x : Vec d => scalarCoeffField a0 x i j :=
      (continuous_apply j).comp ((continuous_apply i).comp hmatrix) |>.measurable
    exact Measurable.ite (measurableSet_openCubeSet Q) hentry measurable_const
  · intro x hx
    have hxc : x ∈ closure (openCubeSet Q) := subset_closure hx
    have hlow : a0 xmin ≤ a0 x := hmin hxc
    have hupp : a0 x ≤ a0 xmax := hmax hxc
    exact (isEllipticMatrix_scalarMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L sample x)).mono
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L sample xmin) hlow hupp

private theorem paperScalarProbe_le_onion_tsum [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (sample : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (n : ℤ) (alpha : ℝ) (e : Vec d) :
    paperScalarProbe (originCube d n) (aCutoffFamily M L sample) alpha e ≤
      (cubeVolume (originCube d n))⁻¹ *
        ∑' p : OnionIndex d n, cubeVolume p.2.1 *
          paperScalarProbe p.2.1 (aCutoffFamily M L sample) alpha e := by
  let pvec : Vec d := (Real.sqrt alpha)⁻¹ • e
  let qvec : Vec d := Real.sqrt alpha • e
  obtain ⟨lam, Lam, hlam, hEll⟩ :=
    exists_isEllipticFieldOn_aCutoff_openCubeSet M L sample (originCube d n)
  have hsub : ∀ p : OnionIndex d n,
      openCubeSet p.2.1 ⊆ openCubeSet (originCube d n) := by
    rintro ⟨t, R⟩ x hx
    exact openCubeSet_originCube_mono (d := d)
      (show n - (t : ℤ) ≤ n by omega)
      (openCubeSet_subset_of_mem_childCubes R.2.1 hx)
  have hcellEll : ∀ p : OnionIndex d n,
      IsEllipticFieldOn lam Lam (openCubeSet p.2.1)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L sample)) :=
    fun p => hEll.mono (measurableSet_openCubeSet p.2.1) (hsub p)
  let K : ℝ := lam⁻¹ * (Lam ^ 2 * vecNormSq pvec + vecNormSq qvec)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (inv_nonneg.mpr hlam.le)
      (add_nonneg (mul_nonneg (sq_nonneg Lam) (vecNormSq_nonneg pvec))
        (vecNormSq_nonneg qvec))
  have hBnonneg : ∀ p : OnionIndex d n,
      0 ≤ paperScalarProbe p.2.1 (aCutoffFamily M L sample) alpha e := by
    intro p
    exact Ch02.responseJ_nonneg (Ch02.cubeDomain p.2.1)
      ((aCutoffFamily M L sample).coeffOn p.2.1) pvec qvec
  have hBle : ∀ p : OnionIndex d n,
      paperScalarProbe p.2.1 (aCutoffFamily M L sample) alpha e ≤ K := by
    intro p
    have hfin : volume (openCubeSet p.2.1) < ⊤ := volume_openCubeSet_lt_top _
    letI : Fact (volume (openCubeSet p.2.1) < ⊤) := ⟨hfin⟩
    unfold paperScalarProbe J
    rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
    exact responseJ_le_plainUpperBound_of_isEllipticFieldOn (hcellEll p)
      (by simpa using! (cubeVolume_pos p.2.1).ne') pvec qvec
  have hUnionSub : (⋃ p : OnionIndex d n, openCubeSet p.2.1) ⊆
      openCubeSet (originCube d n) := Set.iUnion_subset hsub
  have hvolTop : (∑' p : OnionIndex d n, volume (openCubeSet p.2.1)) ≠ ⊤ := by
    rw [← measure_iUnion (onionCells_pairwiseDisjoint (d := d) n)
      (fun p => measurableSet_openCubeSet p.2.1)]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hUnionSub)
      (volume_openCubeSet_lt_top _))
  have hvolSummable : Summable fun p : OnionIndex d n =>
      (volume (openCubeSet p.2.1)).toReal := ENNReal.summable_toReal hvolTop
  have hsum : Summable fun p : OnionIndex d n =>
      (volume (openCubeSet p.2.1)).toReal *
        paperScalarProbe p.2.1 (aCutoffFamily M L sample) alpha e := by
    refine Summable.of_nonneg_of_le
      (fun p => mul_nonneg (ENNReal.toReal_nonneg) (hBnonneg p)) ?_
      (hvolSummable.mul_right K)
    intro p
    exact mul_le_mul_of_nonneg_left (hBle p) ENNReal.toReal_nonneg
  have hmain :=
    LambdaStabilitySupport.responseJ_le_tsum_of_countable_cover
      (ι := OnionIndex d n)
      (V := openCubeSet (originCube d n))
      (a := scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L sample))
      (lam := lam) (Lam := Lam) (p := pvec) (q := qvec)
      (by rw [← ball_cubeCenter_eq_openCubeSet]; exact Metric.isOpen_ball)
      (volume_openCubeSet_lt_top _)
      (by simpa using! (cubeVolume_pos (originCube d n)).ne') hEll
      (fun p => openCubeSet p.2.1)
      (fun p => by change IsOpen (openCubeSet p.2.1)
                   rw [← ball_cubeCenter_eq_openCubeSet]; exact Metric.isOpen_ball)
      (fun p => measurableSet_openCubeSet p.2.1) hsub
      (onionCells_pairwiseDisjoint (d := d) n)
      (fun p => volume_openCubeSet_lt_top p.2.1)
      (fun p => by simpa using! (cubeVolume_pos p.2.1).ne')
      (volume_onion_diff_iUnion_openCubeSet (d := d) n)
      (fun p => paperScalarProbe p.2.1 (aCutoffFamily M L sample) alpha e)
      (fun _ => le_rfl) hsum
  simpa only [pvec, qvec, paperScalarProbe, J,
    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ,
    volume_openCubeSet_toReal] using! hmain

private theorem ofReal_paperScalarProbe_le_onion_tsum [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (sample : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (n : ℤ) (alpha : ℝ) (e : Vec d) :
    ENNReal.ofReal
        (paperScalarProbe (originCube d n) (aCutoffFamily M L sample) alpha e) ≤
      ENNReal.ofReal ((cubeVolume (originCube d n))⁻¹) *
        ∑' p : OnionIndex d n, ENNReal.ofReal (cubeVolume p.2.1) *
          ENNReal.ofReal
            (paperScalarProbe p.2.1 (aCutoffFamily M L sample) alpha e) := by
  have hsub : ∀ p : OnionIndex d n,
      openCubeSet p.2.1 ⊆ openCubeSet (originCube d n) := by
    rintro ⟨t, R⟩ x hx
    exact openCubeSet_originCube_mono (d := d)
      (show n - (t : ℤ) ≤ n by omega)
      (openCubeSet_subset_of_mem_childCubes R.2.1 hx)
  have hUnionSub : (⋃ p : OnionIndex d n, openCubeSet p.2.1) ⊆
      openCubeSet (originCube d n) := Set.iUnion_subset hsub
  have hvolTop : (∑' p : OnionIndex d n, volume (openCubeSet p.2.1)) ≠ ⊤ := by
    rw [← measure_iUnion (onionCells_pairwiseDisjoint (d := d) n)
      (fun p => measurableSet_openCubeSet p.2.1)]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hUnionSub)
      (volume_openCubeSet_lt_top _))
  have hvolSummable : Summable fun p : OnionIndex d n => cubeVolume p.2.1 := by
    simpa only [volume_openCubeSet_toReal] using! ENNReal.summable_toReal hvolTop
  obtain ⟨lam, Lam, hlam, hEll⟩ :=
    exists_isEllipticFieldOn_aCutoff_openCubeSet M L sample (originCube d n)
  let K : ℝ := lam⁻¹ *
    (Lam ^ 2 * vecNormSq ((Real.sqrt alpha)⁻¹ • e) +
      vecNormSq (Real.sqrt alpha • e))
  have hBle : ∀ p : OnionIndex d n,
      paperScalarProbe p.2.1 (aCutoffFamily M L sample) alpha e ≤ K := by
    intro p
    letI : Fact (volume (openCubeSet p.2.1) < ⊤) :=
      ⟨volume_openCubeSet_lt_top _⟩
    unfold paperScalarProbe J
    rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
    exact responseJ_le_plainUpperBound_of_isEllipticFieldOn
      (hEll.mono (measurableSet_openCubeSet p.2.1) (hsub p))
      (by simpa using! (cubeVolume_pos p.2.1).ne') _ _
  have hsummable : Summable fun p : OnionIndex d n =>
      cubeVolume p.2.1 *
        paperScalarProbe p.2.1 (aCutoffFamily M L sample) alpha e := by
    refine Summable.of_nonneg_of_le
      (fun p => mul_nonneg (cubeVolume_nonneg _)
        (Ch02.responseJ_nonneg (Ch02.cubeDomain p.2.1)
          ((aCutoffFamily M L sample).coeffOn p.2.1)
          ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e))) ?_
      (hvolSummable.mul_right K)
    intro p
    exact mul_le_mul_of_nonneg_left (hBle p) (cubeVolume_nonneg _)
  refine le_trans (ENNReal.ofReal_le_ofReal
    (paperScalarProbe_le_onion_tsum M L sample n alpha e)) ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (cubeVolume_nonneg _)),
    ENNReal.ofReal_tsum_of_nonneg _ hsummable]
  · gcongr
    rw [ENNReal.ofReal_mul (cubeVolume_nonneg _)]
  · intro p
    exact mul_nonneg (cubeVolume_nonneg _)
      (Ch02.responseJ_nonneg (Ch02.cubeDomain p.2.1)
        ((aCutoffFamily M L sample).coeffOn p.2.1)
        ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e))

private theorem onionCube_volume_ratio {n : ℤ} {t : ℕ}
    (R : OnionCube d n t) :
    (cubeVolume (originCube d n))⁻¹ * cubeVolume R.1 =
      (3 : ℝ) ^ (-(d : ℝ) * ((t : ℝ) + 1)) := by
  rw [cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale, onionCube_scale]
  simp only [originCube]
  rw [← Real.rpow_intCast 3, ← Real.rpow_intCast 3]
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (n : ℝ)),
    ← Real.rpow_natCast ((3 : ℝ) ^ ((n - 1 - (t : ℤ) : ℤ) : ℝ))]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

private theorem onion_card_weight_identity (d t : ℕ) :
    ((3 ^ d : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * ((t : ℝ) + 1))) =
      ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * (t : ℝ))) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast 3, ← Real.rpow_add (by norm_num)]
  congr 1
  ring

private theorem onionCube_card_le (d : ℕ) (n : ℤ) (t : ℕ) :
    Fintype.card (OnionCube d n t) ≤ 3 ^ d := by
  calc
    Fintype.card (OnionCube d n t) ≤
        Fintype.card {R : TriadicCube d //
          R ∈ childCubes (originCube d (n - (t : ℤ)))} :=
      Fintype.card_le_of_injective
        (fun R : OnionCube d n t =>
          (⟨R.1, R.2.1⟩ : {R : TriadicCube d //
            R ∈ childCubes (originCube d (n - (t : ℤ))) }))
        (by
          intro R S h
          apply Subtype.ext
          exact congrArg
            (fun T : {T : TriadicCube d //
              T ∈ childCubes (originCube d (n - (t : ℤ)))} => T.1) h)
    _ = (childCubes (originCube d (n - (t : ℤ)))).card := by simp
    _ = 3 ^ d := childCubes_card _

private theorem onionLayer_le_annulusMax [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (n : ℤ) (t : ℕ) (alpha : ℝ)
    (e : {e : Vec d // vecNormSq e = 1}) :
    ∑' R : OnionCube d n t,
        ENNReal.ofReal ((cubeVolume (originCube d n))⁻¹) *
          (ENNReal.ofReal (cubeVolume R.1) *
            ENNReal.ofReal
              (paperScalarProbe R.1
                (aCutoffFamily M L (translatePotentialSample z ω)) alpha e)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * (t : ℝ))) *
        annulusMax (section6LocalProbeMax M L ω z alpha)
          (n - 1 - (t : ℤ)) := by
  rw [tsum_fintype]
  calc
    ∑ R : OnionCube d n t,
        ENNReal.ofReal ((cubeVolume (originCube d n))⁻¹) *
          (ENNReal.ofReal (cubeVolume R.1) *
            ENNReal.ofReal
              (paperScalarProbe R.1
                (aCutoffFamily M L (translatePotentialSample z ω)) alpha e))
      ≤ ∑ _R : OnionCube d n t,
          ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * ((t : ℝ) + 1))) *
            annulusMax (section6LocalProbeMax M L ω z alpha)
              (n - 1 - (t : ℤ)) := by
        refine Finset.sum_le_sum fun R _ => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul
          (inv_nonneg.mpr (cubeVolume_nonneg _)), onionCube_volume_ratio]
        gcongr
        calc
            ENNReal.ofReal
                (paperScalarProbe R.1
                  (aCutoffFamily M L (translatePotentialSample z ω)) alpha e) =
                ENNReal.ofReal
                  (paperScalarProbe (originCube d R.1.scale)
                    (aCutoffFamily M L
                      (translatePotentialSample (triadicCubeShift R.1)
                        (translatePotentialSample z ω))) alpha e) := by
                  rw [paperScalarProbe_aCutoffFamily_eq_origin]
            _ ≤ section6LocalProbeMax M L ω z alpha R.1 :=
              le_iSup (fun e : {e : Vec d // vecNormSq e = 1} =>
                ENNReal.ofReal
                  (paperScalarProbe (originCube d R.1.scale)
                    (aCutoffFamily M L
                      (translatePotentialSample (triadicCubeShift R.1)
                        (translatePotentialSample z ω))) alpha e)) e
            _ ≤ annulusMax (section6LocalProbeMax M L ω z alpha)
                (n - 1 - (t : ℤ)) := by
              exact le_iSup (fun S : {S : TriadicCube d //
                S.scale = n - 1 - (t : ℤ) ∧
                  triadicCubeShift S ∈
                    cube d (n - 1 - (t : ℤ) + 1) \
                      cube d (n - 1 - (t : ℤ))} =>
                  section6LocalProbeMax M L ω z alpha S.1)
                ⟨R.1, onionCube_scale R,
                  by
                    have heq : n - 1 - (t : ℤ) + 1 = n - (t : ℤ) := by ring
                    rw [heq]
                    exact onionCube_shift_mem_annulus R⟩
    _ = (Fintype.card (OnionCube d n t) : ℝ≥0∞) *
          (ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * ((t : ℝ) + 1))) *
            annulusMax (section6LocalProbeMax M L ω z alpha)
              (n - 1 - (t : ℤ))) := by simp
    _ ≤ ((3 ^ d : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * ((t : ℝ) + 1))) *
            annulusMax (section6LocalProbeMax M L ω z alpha)
              (n - 1 - (t : ℤ))) := by
        gcongr
        exact_mod_cast onionCube_card_le d n t
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * (t : ℝ))) *
          annulusMax (section6LocalProbeMax M L ω z alpha)
            (n - 1 - (t : ℤ)) := by
        rw [← mul_assoc, onion_card_weight_identity]

private theorem translatePotentialSample_originCubeShift
    (n : ℤ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    translatePotentialSample (triadicCubeShift (originCube d n)) ω = ω := by
  funext k
  apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
  intro x
  have hz : triadicCubeShift (originCube d n) = 0 := by
    funext i
    simp [triadicCubeShift, originCube]
  simp only [translatePotentialSample,
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply, hz, add_zero]

/-- Countable response subadditivity over the triadic onion surrounding the
centered cube, in the exact geometric-weight form used in Section 6. -/
theorem section6LocalProbeMax_originCube_le_onion [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (alpha : ℝ) (n : ℤ) :
    section6LocalProbeMax M L ω z alpha (originCube d n) ≤
      ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * (t : ℝ))) *
        annulusMax (section6LocalProbeMax M L ω z alpha)
          (n - 1 - (t : ℤ)) := by
  unfold section6LocalProbeMax
  rw [translatePotentialSample_originCubeShift]
  refine iSup_le fun e => ?_
  calc
    ENNReal.ofReal
        (paperScalarProbe (originCube d n)
          (aCutoffFamily M L (translatePotentialSample z ω)) alpha e) ≤
        ENNReal.ofReal ((cubeVolume (originCube d n))⁻¹) *
          ∑' p : OnionIndex d n, ENNReal.ofReal (cubeVolume p.2.1) *
            ENNReal.ofReal
              (paperScalarProbe p.2.1
                (aCutoffFamily M L (translatePotentialSample z ω)) alpha e) :=
      ofReal_paperScalarProbe_le_onion_tsum M L
        (translatePotentialSample z ω) n alpha e
    _ = ∑' t : ℕ, ∑' R : OnionCube d n t,
          ENNReal.ofReal ((cubeVolume (originCube d n))⁻¹) *
            (ENNReal.ofReal (cubeVolume R.1) *
              ENNReal.ofReal
                (paperScalarProbe R.1
                  (aCutoffFamily M L (translatePotentialSample z ω)) alpha e)) := by
      rw [ENNReal.tsum_sigma']
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun t => ?_
      rw [← ENNReal.tsum_mul_left]
    _ ≤ ∑' t : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℝ) * (t : ℝ))) *
          annulusMax (section6LocalProbeMax M L ω z alpha)
            (n - 1 - (t : ℤ)) := by
      exact ENNReal.tsum_le_tsum fun t =>
        onionLayer_le_annulusMax M L ω z n t alpha e

/-- One-step response subadditivity: one child realizes at least the parent response. -/
theorem section6LocalProbeMax_le_child [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) (alpha : ℝ)
    (R : TriadicCube d) :
    ∃ R' ∈ Homogenization.childCubes R,
      section6LocalProbeMax M L ω z alpha R ≤
        section6LocalProbeMax M L ω z alpha R' := by
  let sample := translatePotentialSample z ω
  obtain ⟨R', hR', hmax⟩ := (Homogenization.childCubes R).exists_max_image
    (section6LocalProbeMax M L ω z alpha)
    (Homogenization.childCubes_nonempty R)
  refine ⟨R', hR', ?_⟩
  unfold section6LocalProbeMax
  refine iSup_le fun e => ?_
  have hsub := cutoffResponseOnCube_le_descendantsAverage M L
    ((Real.sqrt alpha)⁻¹ • (e : Vec d)) (Real.sqrt alpha • (e : Vec d))
    R 1 sample
  have hparent :
      paperScalarProbe (originCube d R.scale)
          (aCutoffFamily M L
            (translatePotentialSample (triadicCubeShift R) sample)) alpha e =
        cutoffResponseOnCube M L ((Real.sqrt alpha)⁻¹ • (e : Vec d))
          (Real.sqrt alpha • (e : Vec d)) R sample := by
    rw [← paperScalarProbe_aCutoffFamily_eq_origin M L sample R alpha e]
    rfl
  rw [hparent]
  refine le_trans (ENNReal.ofReal_le_ofReal hsub) ?_
  unfold descendantsAverage
  have hcardpos : (0 : ℝ) < ((descendantsAtDepth R 1).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty R 1)
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcardpos.le),
    ENNReal.ofReal_inv_of_pos hcardpos, ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg]
  · calc
      ((descendantsAtDepth R 1).card : ℝ≥0∞)⁻¹ *
          ∑ S ∈ descendantsAtDepth R 1,
            ENNReal.ofReal (cutoffResponseOnCube M L
              ((Real.sqrt alpha)⁻¹ • (e : Vec d))
              (Real.sqrt alpha • (e : Vec d)) S sample)
        ≤ ((descendantsAtDepth R 1).card : ℝ≥0∞)⁻¹ *
            ∑ _S ∈ descendantsAtDepth R 1,
              section6LocalProbeMax M L ω z alpha R' := by
          gcongr with S hS
          have hSchild : S ∈ childCubes R := by
            simpa [descendantsAtDepth_one] using! hS
          calc
            ENNReal.ofReal (cutoffResponseOnCube M L
                ((Real.sqrt alpha)⁻¹ • (e : Vec d))
                (Real.sqrt alpha • (e : Vec d)) S sample) =
                ENNReal.ofReal
                  (paperScalarProbe (originCube d S.scale)
                    (aCutoffFamily M L
                      (translatePotentialSample (triadicCubeShift S) sample)) alpha e) := by
              rw [← paperScalarProbe_aCutoffFamily_eq_origin M L sample S alpha e]
              rfl
            _ ≤ section6LocalProbeMax M L ω z alpha S :=
              le_iSup (fun e : {e : Vec d // vecNormSq e = 1} =>
                ENNReal.ofReal
                  (paperScalarProbe (originCube d S.scale)
                    (aCutoffFamily M L
                      (translatePotentialSample (triadicCubeShift S)
                        (translatePotentialSample z ω))) alpha e)) e
            _ ≤ section6LocalProbeMax M L ω z alpha R' := hmax S hSchild
      _ = section6LocalProbeMax M L ω z alpha R' := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [← mul_assoc, ENNReal.inv_mul_cancel]
          · simp
          · exact_mod_cast Finset.card_ne_zero.mpr
              (descendantsAtDepth_nonempty R 1)
          · exact ENNReal.coe_ne_top
  · intro S hS
    exact Ch02.responseJ_nonneg (Ch02.cubeDomain S)
      ((aCutoffFamily M L sample).coeffOn S)
      ((Real.sqrt alpha)⁻¹ • (e : Vec d)) (Real.sqrt alpha • (e : Vec d))

/-- The Section 6 error carrier in annular form, with countable onion
subadditivity discharged from the response theory. -/
theorem section6HomogenizationError_le_annularSup
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (hd : 1 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) :
    ENNReal.ofReal (section6HomogenizationError M s L m ω z) ≤
      (64 * annularSup s (m : ℤ)
          (section6LocalProbeMax M L ω z
            (tailCoefficientCubeAverage M L m
              (translatePotentialSample z ω)))) ^ (1 / 2 : ℝ) := by
  letI : NeZero d := ⟨by omega⟩
  apply section6HomogenizationError_le_annularSup_of_countableSubadditivity
    hs hs2 hd M L m ω z
  intro n _hn
  exact section6LocalProbeMax_originCube_le_onion M L ω z
    (tailCoefficientCubeAverage M L m (translatePotentialSample z ω)) n

/-- The Section 6 error carrier in the refined annular form, with both the
countable onion and one-child subadditivity hypotheses discharged. -/
theorem section6HomogenizationError_le_annularSupTwo
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (hd : 1 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) :
    ENNReal.ofReal (section6HomogenizationError M s L m ω z) ≤
      (192 * annularSupTwo s (m : ℤ)
          (section6LocalProbeMax M L ω z
            (tailCoefficientCubeAverage M L m
              (translatePotentialSample z ω)))) ^ (1 / 2 : ℝ) := by
  letI : NeZero d := ⟨by omega⟩
  apply section6HomogenizationError_le_annularSupTwo_of_subadditivity
    hs hs2 hd M L m ω z
  · intro n _hn
    exact section6LocalProbeMax_originCube_le_onion M L ω z
      (tailCoefficientCubeAverage M L m (translatePotentialSample z ω)) n
  · intro R
    exact section6LocalProbeMax_le_child M L ω z
      (tailCoefficientCubeAverage M L m (translatePotentialSample z ω)) R

end

end SubdiffusiveProcess.CoarseGrainingVocab
