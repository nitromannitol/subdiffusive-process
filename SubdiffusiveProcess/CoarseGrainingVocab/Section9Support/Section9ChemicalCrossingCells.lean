import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingProduct




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The snapping grid -/

/-- The mesh of the scale-`j` grid of admissible cell centres. -/
def crossMesh (Cdep j : ℕ) : ℕ := 2 * (Cdep * 3 ^ j) + 1

theorem crossMesh_pos (Cdep j : ℕ) : 0 < crossMesh Cdep j := by
  unfold crossMesh; omega

/-- The scale-`j` grid point with index `a`. -/
def crossGrid (Cdep j : ℕ) (a : Lattice d) : Lattice d :=
  fun i => (crossMesh Cdep j : ℤ) * a i

/-- The index of a grid point nearest to `u`. -/
def crossSnap (Cdep j : ℕ) (u : Lattice d) : Lattice d :=
  fun i => (u i + (Cdep * 3 ^ j : ℕ)) / (crossMesh Cdep j : ℤ)

/-- Every site is within the thickening radius `Cdep 3^j` of its snapped grid
point. -/
theorem latticeDist_crossGrid_crossSnap (Cdep j : ℕ) (u : Lattice d) :
    latticeDist u (crossGrid Cdep j (crossSnap Cdep j u)) ≤ Cdep * 3 ^ j := by
  set r : ℕ := Cdep * 3 ^ j with hr
  set m : ℤ := (crossMesh Cdep j : ℤ) with hm
  have hmval : m = 2 * (r : ℤ) + 1 := by
    rw [hm, hr, crossMesh]; push_cast; ring
  have hmpos : 0 < m := by rw [hmval]; positivity
  refine latticeDist_le_iff.mpr fun i => ?_
  have hcoord : (crossGrid Cdep j (crossSnap Cdep j u) : Lattice d) i =
      m * ((u i + (r : ℤ)) / m) := rfl
  obtain ⟨M, hM⟩ : ∃ M : ℤ, m * ((u i + (r : ℤ)) / m) = M := ⟨_, rfl⟩
  have hdiv : M + (u i + (r : ℤ)) % m = u i + (r : ℤ) := by
    rw [← hM]; exact Int.mul_ediv_add_emod _ _
  have hnn : 0 ≤ (u i + (r : ℤ)) % m := Int.emod_nonneg _ (ne_of_gt hmpos)
  have hlt : (u i + (r : ℤ)) % m < m := Int.emod_lt_of_pos _ hmpos
  rw [hcoord, hM]
  omega

/-- The parity colour of a grid index. -/
def crossColor (a : Lattice d) : Fin d → Bool := fun i => decide (a i % 2 = 0)

/-- The grid index of a cell (`0` for a good vertex). -/
def cellIndexAux (d : ℕ) : (ℕ × Lattice d) ⊕ Lattice d → Lattice d
  | Sum.inl p => p.2
  | Sum.inr _ => 0

/-- Two distinct grid indices of the same parity class give grid points at
distance at least twice the mesh. -/
theorem two_mul_crossMesh_le_latticeDist_crossGrid {Cdep j : ℕ} {a b : Lattice d}
    (hne : a ≠ b) (hcol : crossColor a = crossColor b) :
    2 * crossMesh Cdep j ≤ latticeDist (crossGrid Cdep j a) (crossGrid Cdep j b) := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
    by_contra hcon
    exact hne (funext fun i => not_not.mp fun h => hcon ⟨i, h⟩)
  have hpar : a i % 2 = b i % 2 := by
    have h := congrFun hcol i
    simp only [crossColor, decide_eq_decide] at h
    rcases Int.emod_two_eq_zero_or_one (a i) with ha | ha <;>
      rcases Int.emod_two_eq_zero_or_one (b i) with hb | hb <;>
        simp [ha, hb] at h ⊢
  have htwo : 2 ≤ (a i - b i).natAbs := by
    have hmod : (a i - b i) % 2 = 0 := by omega
    have hnz : a i - b i ≠ 0 := sub_ne_zero_of_ne hi
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hmod
    have hkne : k ≠ 0 := by rintro rfl; simp at hk; exact hnz hk
    have : 1 ≤ k.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_eq_zero.not.mpr hkne)
    rw [hk, Int.natAbs_mul]
    simpa using Nat.mul_le_mul_left 2 this
  refine le_trans ?_ (coord_le_latticeDist (crossGrid Cdep j a) (crossGrid Cdep j b) i)
  have hval : ((crossGrid Cdep j a : Lattice d) i - (crossGrid Cdep j b : Lattice d) i) =
      (crossMesh Cdep j : ℤ) * (a i - b i) := by
    simp only [crossGrid]; ring
  rw [hval, Int.natAbs_mul, Int.natAbs_natCast]
  calc 2 * crossMesh Cdep j = crossMesh Cdep j * 2 := by ring
    _ ≤ crossMesh Cdep j * (a i - b i).natAbs := Nat.mul_le_mul_left _ htwo

/-! ## Cells -/

/-- A **cell** of a crossing certificate: either an occurring bad event of some
scale, recorded by its scale and the index of its snapped grid centre
(`Sum.inl`), or a single good vertex (`Sum.inr`). -/
abbrev CrossCell (d : ℕ) : Type := (ℕ × Lattice d) ⊕ Lattice d

/-- The parity colour of a cell. -/
def cellColor (c : CrossCell d) : Fin d → Bool := crossColor (cellIndexAux d c)

/-- The scale of a cell (`0` for a good vertex). -/
def cellScale : CrossCell d → ℕ
  | Sum.inl p => p.1
  | Sum.inr _ => 0

/-- The centre of a cell. -/
def cellCenter (Cdep : ℕ) : CrossCell d → Lattice d
  | Sum.inl p => crossGrid Cdep p.1 p.2
  | Sum.inr v => v

/-- The radius of a cell: a good vertex is a point, an event cell covers the
influence box of every event it can carry. -/
def cellRadius (Cbox Cdep : ℕ) : CrossCell d → ℕ
  | Sum.inl p => (Cbox + Cdep) * 3 ^ p.1
  | Sum.inr _ => 0

/-- The event carried by a cell: the thickened scale-`j` event at the grid
centre for an event cell, and no condition at all for a good vertex. -/
def cellOccurs (E : ℕ → Lattice d → Set Ω) (Cdep : ℕ) : CrossCell d → Set Ω
  | Sum.inl p => influenceFailure (E p.1) (Cdep * 3 ^ p.1) (crossGrid Cdep p.1 p.2)
  | Sum.inr _ => Set.univ

/-- The weight of a cell: its `2^d`-th power dominates the probability of the
cell's event, which is what the parity colouring costs. -/
def cellWeight (dim Cdep : ℕ) (Cprob cprob q : ℝ) : CrossCell d → ℝ≥0∞
  | Sum.inl p => ENNReal.ofReal
      ((((2 * (Cdep * 3 ^ p.1) + 1) ^ dim : ℕ) : ℝ) * max 1 Cprob *
        Real.exp (-(cprob / 2 ^ dim) * q * 3 ^ ((3 : ℝ) * p.1 / 2)))
  | Sum.inr _ => 1

/-- The event that every cell of a chain occurs. -/
def chainEvent (E : ℕ → Lattice d → Set Ω) (Cdep : ℕ) (L : List (CrossCell d)) :
    Set Ω := {ω | ∀ c ∈ L, ω ∈ cellOccurs E Cdep c}

/-! ## The probability of a chain event -/

theorem measurableSet_cellOccurs_support [MeasurableSpace Ω]
    (E : ℕ → Lattice d → Set Ω) (Cdep : ℕ) (c : CrossCell d) :
    MeasurableSet[eventFieldSigma (E (cellScale c))
      (latticeBallFinset (cellCenter Cdep c) (Cdep * 3 ^ cellScale c) :
        Set (Lattice d))] (cellOccurs E Cdep c) := by
  cases c with
  | inl p =>
      refine MeasurableSet.biUnion (Finset.countable_toSet _) fun u hu => ?_
      exact measurableSet_event_of_mem (Finset.mem_coe.mpr hu)
  | inr v => exact MeasurableSet.univ

theorem measure_cellOccurs_le_pow [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} (Cdep : ℕ)
    {Cprob cprob q : ℝ}
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (c : CrossCell d) :
    mu (cellOccurs E Cdep c) ≤ cellWeight d Cdep Cprob cprob q c ^ (2 ^ d) := by
  cases c with
  | inr v => simp [cellOccurs, cellWeight]
  | inl p =>
      obtain ⟨j, a⟩ := p
      set r : ℕ := Cdep * 3 ^ j with hrdef
      set N : ℕ := (2 * r + 1) ^ d with hNdef
      set t : ℝ := (3 : ℝ) ^ ((3 : ℝ) * j / 2) with htdef
      have htpos : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
      have hKpos : (0 : ℝ) < 2 ^ d := by positivity
      have hbase : mu (cellOccurs E Cdep (Sum.inl (j, a))) ≤
          (N : ℝ≥0∞) * ENNReal.ofReal (Cprob * Real.exp (-cprob * q * t)) := by
        have h := measure_influenceFailure_le (μ := mu) (E j) r (crossGrid Cdep j a)
          (ENNReal.ofReal (Cprob * Real.exp (-cprob * q * t))) (fun u => hprob j u)
        rw [nsmul_eq_mul] at h
        exact h
      refine hbase.trans ?_
      have hA : (1 : ℝ) ≤ (N : ℝ) * max 1 Cprob := by
        have h1 : (1 : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
        nlinarith [le_max_left (1 : ℝ) Cprob]
      have hCle : Cprob ≤ max 1 Cprob := le_max_right _ _
      have hexpalg : ((2 ^ d : ℕ) : ℝ) * (-(cprob / 2 ^ d) * q * t) = -cprob * q * t := by
        have h2 : ((2 : ℝ) ^ d) ≠ 0 := by positivity
        push_cast
        field_simp
      have hval : ((N : ℝ) * max 1 Cprob *
          Real.exp (-(cprob / 2 ^ d) * q * t)) ^ (2 ^ d) =
          ((N : ℝ) * max 1 Cprob) ^ (2 ^ d) * Real.exp (-cprob * q * t) := by
        rw [mul_pow, ← Real.exp_nat_mul, hexpalg]
      have hpowA : (N : ℝ) * Cprob ≤ ((N : ℝ) * max 1 Cprob) ^ (2 ^ d) := by
        have h1 : (N : ℝ) * Cprob ≤ (N : ℝ) * max 1 Cprob := by
          have : (0 : ℝ) ≤ (N : ℝ) := by positivity
          nlinarith
        refine h1.trans ?_
        exact le_self_pow₀ hA (by positivity : (0 : ℕ) < 2 ^ d).ne'
      have hfinal : (N : ℝ) * (Cprob * Real.exp (-cprob * q * t)) ≤
          ((N : ℝ) * max 1 Cprob *
            Real.exp (-(cprob / 2 ^ d) * q * t)) ^ (2 ^ d) := by
        rw [hval]
        have hexp : (0 : ℝ) < Real.exp (-cprob * q * t) := Real.exp_pos _
        nlinarith
      calc (N : ℝ≥0∞) * ENNReal.ofReal (Cprob * Real.exp (-cprob * q * t))
          = ENNReal.ofReal ((N : ℝ) * (Cprob * Real.exp (-cprob * q * t))) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (((N : ℝ) * max 1 Cprob *
              Real.exp (-(cprob / 2 ^ d) * q * t)) ^ (2 ^ d)) :=
            ENNReal.ofReal_le_ofReal hfinal
        _ = cellWeight d Cdep Cprob cprob q (Sum.inl (j, a)) ^ (2 ^ d) := by
            rw [cellWeight, ← ENNReal.ofReal_pow (by positivity)]

/-- **The probability of a chain event, in terms of the cell weights.**

Every cell of the chain contributes its weight; the parity colouring is what
turns the `2^d`-th power of `measure_cellOccurs_le_pow` into a clean product. -/
theorem measure_chainEvent_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} (Cdep : ℕ)
    {Cprob cprob q : ℝ}
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (L : List (CrossCell d)) (hnd : L.Nodup) :
    mu (chainEvent E Cdep L) ≤ (L.map (cellWeight d Cdep Cprob cprob q)).prod := by
  classical
  set S : Finset (CrossCell d) := L.toFinset.filter (fun c => c.isLeft = true) with hS
  have hchain : chainEvent E Cdep L = ⋂ c ∈ S, cellOccurs E Cdep c := by
    ext ω
    simp only [chainEvent, Set.mem_setOf_eq, Set.mem_iInter, hS, Finset.mem_filter,
      List.mem_toFinset]
    constructor
    · intro h c hc; exact h c hc.1
    · intro h c hc
      cases c with
      | inl p => exact h _ ⟨hc, rfl⟩
      | inr v => exact Set.mem_univ _
  -- the product over one colour class
  have hclass : ∀ γ : Fin d → Bool,
      mu (⋂ c ∈ S, cellOccurs E Cdep c) ≤
        ∏ c ∈ S.filter (fun c => cellColor c = γ),
          mu (cellOccurs E Cdep c) := by
    intro γ
    set T : Finset (CrossCell d) :=
      S.filter (fun c => cellColor c = γ) with hT
    have hmono : (⋂ c ∈ S, cellOccurs E Cdep c) ⊆ ⋂ c ∈ T, cellOccurs E Cdep c := by
      refine Set.iInter₂_mono' fun c hc => ⟨c, (Finset.mem_filter.mp hc).1, le_rfl⟩
    refine (measure_mono hmono).trans_eq ?_
    refine measure_biInter_multiscale_thickened_eq_prod mu E Cdep hsc hr T cellScale
      (cellCenter Cdep) (fun j => Cdep * 3 ^ j) (cellOccurs E Cdep)
      (fun c _ => measurableSet_cellOccurs_support E Cdep c) ?_
    intro a ha b hb hab hscale
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have haL : a.isLeft = true := (Finset.mem_filter.mp ha'.1).2
    have hbL : b.isLeft = true := (Finset.mem_filter.mp hb'.1).2
    obtain ⟨pa, rfl⟩ : ∃ p, a = Sum.inl p := by
      cases a with
      | inl p => exact ⟨p, rfl⟩
      | inr v => simp at haL
    obtain ⟨pb, rfl⟩ : ∃ p, b = Sum.inl p := by
      cases b with
      | inl p => exact ⟨p, rfl⟩
      | inr v => simp at hbL
    have hj : pa.1 = pb.1 := hscale
    have hidx : pa.2 ≠ pb.2 := by
      intro h
      exact hab (by rw [← Prod.ext hj h])
    have hcol : crossColor pa.2 = crossColor pb.2 := by
      have h1 : cellColor (Sum.inl pa : CrossCell d) = γ := ha'.2
      have h2 : cellColor (Sum.inl pb : CrossCell d) = γ := hb'.2
      simp only [cellColor, cellIndexAux] at h1 h2
      rw [h1, h2]
    have hsep := two_mul_crossMesh_le_latticeDist_crossGrid (Cdep := Cdep)
      (j := pa.1) hidx hcol
    have hcenter : latticeDist (cellCenter Cdep (Sum.inl pa))
        (cellCenter Cdep (Sum.inl pb)) =
        latticeDist (crossGrid Cdep pa.1 pa.2) (crossGrid Cdep pa.1 pb.2) := by
      simp only [cellCenter, hj]
    rw [hcenter]
    refine lt_of_lt_of_le ?_ hsep
    show 2 * (Cdep * 3 ^ cellScale (Sum.inl pa)) + Cdep * 3 ^ cellScale (Sum.inl pa) <
      2 * crossMesh Cdep pa.1
    simp only [cellScale, crossMesh]
    omega
  -- multiply the colour bounds
  have hcard : Fintype.card (Fin d → Bool) = 2 ^ d := by
    simp
  have hkey : mu (⋂ c ∈ S, cellOccurs E Cdep c) ^ (2 ^ d) ≤
      ∏ c ∈ S, mu (cellOccurs E Cdep c) := by
    have hprodcol := Finset.prod_le_prod' (f := fun _ : Fin d → Bool =>
        mu (⋂ c ∈ S, cellOccurs E Cdep c))
      (g := fun γ : Fin d → Bool =>
        ∏ c ∈ S.filter (fun c => cellColor c = γ),
          mu (cellOccurs E Cdep c)) (s := (Finset.univ : Finset (Fin d → Bool)))
      (fun γ _ => hclass γ)
    rw [Finset.prod_const, Finset.card_univ, hcard] at hprodcol
    refine hprodcol.trans (le_of_eq ?_)
    exact Finset.prod_fiberwise_of_maps_to (fun c _ => Finset.mem_univ _) _
  have hpow : ∏ c ∈ S, mu (cellOccurs E Cdep c) ≤
      (∏ c ∈ S, cellWeight d Cdep Cprob cprob q c) ^ (2 ^ d) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_le_prod' fun c _ =>
      measure_cellOccurs_le_pow mu Cdep hprob c
  have hle : mu (⋂ c ∈ S, cellOccurs E Cdep c) ≤
      ∏ c ∈ S, cellWeight d Cdep Cprob cprob q c :=
    (ENNReal.pow_le_pow_left_iff (n := 2 ^ d)
      (by positivity : (0 : ℕ) < 2 ^ d).ne').mp (hkey.trans hpow)
  rw [hchain]
  refine hle.trans (le_of_eq ?_)
  have hfilter : ∏ c ∈ S, cellWeight d Cdep Cprob cprob q c =
      ∏ c ∈ L.toFinset, cellWeight d Cdep Cprob cprob q c := by
    rw [hS]
    refine Finset.prod_filter_of_ne ?_
    intro c _ hne
    cases c with
    | inl p => rfl
    | inr v => exact absurd rfl hne
  rw [hfilter, List.prod_toFinset _ hnd]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
