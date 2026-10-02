import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedSourceParentReadout

/-!
# Bounded multiplicity of the centred parents of the retained source cells

Route (1) of `provider-43` §6 indexes the two-radius Neumann family over the
**retained source cells** `oneStepRetainedSourceCells K source N` — the cells
at the source scale whose *own centred* parent of scale `source + N` still
fits inside the ambient cube.  For those cells `hhalf` and `hinner` are free
(`oneStepNestedSourceParentGeometry_of_mem`), because a cell is concentric in
its own centred parent; the only thing the committed overlap machinery does
not supply is the **outer** harmonic budget, which needs the parents to have
bounded multiplicity.

That is what this module proves.  The centred parents have side `3 ^ (source
+ N)` and their centres sit on the source-scale lattice `3 ^ source · ℤ^d`, so
the family splits into `(3 ^ N) ^ d` subfamilies — one per residue class of
the cell index modulo `3 ^ N` — each of which is *pairwise disjoint*.  Summing
the class bounds gives multiplicity `(3 ^ N) ^ d`, and the normalization
against the full source-cell count

```
  ((3 ^ d) ^ (K - source)) ⁻¹ · (3 ^ (source + N)) ^ (-d) · (3 ^ N) ^ d
    = (3 ^ K) ^ (-d)
```

leaves the constant **exactly one**.  In particular the estimate is uniform in
`K` and in `N`.
-/

open MeasureTheory Homogenization
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-! ## Membership in a centred parent -/

theorem mem_oneStepCenteredParent_iff (z : Vec d) (m : ℤ) (x : Vec d) :
    x ∈ oneStepCenteredParent z m ↔
      ∀ i, z i - cubeScaleFactor (originCube d m) / 2 < x i ∧
        x i < z i + cubeScaleFactor (originCube d m) / 2 := by
  rw [oneStepCenteredParent, translateSet_openCubeSet_originCube_eq_axisCube,
    axisCube, Set.mem_univ_pi]
  constructor
  · intro h i
    have hi := h i
    rw [Set.mem_Ioo] at hi
    simp only [oneStepCenteredAxisCorner] at hi
    constructor <;> linarith [hi.1, hi.2]
  · intro h i
    have hi := h i
    rw [Set.mem_Ioo]
    simp only [oneStepCenteredAxisCorner]
    constructor <;> linarith [hi.1, hi.2]

theorem measurableSet_oneStepCenteredParent (z : Vec d) (m : ℤ) :
    MeasurableSet (oneStepCenteredParent z m) := by
  rw [oneStepCenteredParent, translateSet_openCubeSet_originCube_eq_axisCube,
    axisCube]
  exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo

/-- A cube's centre lies in its own open cube. -/
theorem cubeCenter_mem_openCubeSet (R : TriadicCube d) :
    cubeCenter R ∈ openCubeSet R := by
  intro i
  have hpos : (0 : ℝ) < cubeScaleFactor R := by
    simpa [cubeScaleFactor] using (zpow_pos (by norm_num : (0 : ℝ) < 3) R.scale)
  simp only [cubeCenter]
  constructor <;> nlinarith [hpos]

/-- **Sub-parent containment.**  The parent centred at `c` one scale below sits
inside the parent centred at `z`, as soon as `c` itself lies in the
scale-`(mm - 1)` parent at `z`.  This is the geometric core of the `a`-free
harmonic estimate: for a cell `R` inside a cube `S` of scale `mm - 1` centred
at `z`, the cell-centred sub-parent of scale `mm - 1` still fits inside the
scale-`mm` parent, because `3 ^ (mm - 1) = 3 ^ mm / 3 < 3 ^ mm / 2`. -/
theorem oneStepCenteredParent_subset_of_mem
    {z c : Vec d} {mm : ℤ} (hc : c ∈ oneStepCenteredParent z (mm - 1)) :
    oneStepCenteredParent c (mm - 1) ⊆ oneStepCenteredParent z mm := by
  have hside : cubeScaleFactor (originCube d (mm - 1)) * 3 =
      cubeScaleFactor (originCube d mm) := by
    simp only [cubeScaleFactor, originCube]
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    field_simp
  have hpos : (0 : ℝ) < cubeScaleFactor (originCube d (mm - 1)) := by
    simpa [cubeScaleFactor] using
      (zpow_pos (by norm_num : (0 : ℝ) < 3) (mm - 1))
  rw [mem_oneStepCenteredParent_iff] at hc
  intro x hx
  rw [mem_oneStepCenteredParent_iff] at hx
  rw [mem_oneStepCenteredParent_iff]
  intro i
  have h1 := hx i
  have h2 := hc i
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, hside, hpos]

/-! ## Disjointness inside a residue class -/

/-- Two distinct cells of the same scale whose indices agree modulo `3 ^ N`
have disjoint centred parents of scale `source + N`. -/
theorem disjoint_oneStepCenteredParent_of_index_modEq
    {source : ℤ} {N : ℕ} {R R' : TriadicCube d}
    (hR : R.scale = source) (hR' : R'.scale = source) (hne : R ≠ R')
    (hmod : ∀ i, (R.index i : ℤ) ≡ (R'.index i : ℤ) [ZMOD ((3 : ℤ) ^ N)]) :
    Disjoint (oneStepCenteredParent (cubeCenter R) (source + (N : ℤ)))
      (oneStepCenteredParent (cubeCenter R') (source + (N : ℤ))) := by
  -- a coordinate where the indices differ
  obtain ⟨i, hi⟩ : ∃ i, R.index i ≠ R'.index i := by
    by_contra hcon
    push_neg at hcon
    refine hne ?_
    cases R with
    | mk s₁ i₁ =>
      cases R' with
      | mk s₂ i₂ =>
        simp only [TriadicCube.mk.injEq]
        simp only at hR hR'
        exact ⟨by omega, funext hcon⟩
  have hdvd : ((3 : ℤ) ^ N) ∣ (R'.index i - R.index i) := (hmod i).dvd
  have hnz : R'.index i - R.index i ≠ 0 := by
    intro h
    exact hi (by omega)
  have hge : ((3 : ℤ) ^ N) ≤ |R'.index i - R.index i| :=
    Int.le_of_dvd (abs_pos.mpr hnz) ((dvd_abs _ _).mpr hdvd)
  -- transfer to the real centres
  have hpos : (0 : ℝ) < (3 : ℝ) ^ source := zpow_pos (by norm_num) _
  have hgeR : ((3 : ℝ) ^ N) ≤ |(R'.index i : ℝ) - (R.index i : ℝ)| := by
    have := hge
    have hcast : ((3 : ℝ) ^ N) ≤ |((R'.index i - R.index i : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast this
    simpa only [Int.cast_sub] using hcast
  have hside : cubeScaleFactor (originCube d (source + (N : ℤ))) =
      (3 : ℝ) ^ source * (3 : ℝ) ^ N := by
    simp only [cubeScaleFactor, originCube]
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  have hcentre : ∀ (T : TriadicCube d), T.scale = source →
      cubeCenter T i = (T.index i : ℝ) * (3 : ℝ) ^ source := by
    intro T hT
    simp only [cubeCenter, cubeScaleFactor, hT]
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_oneStepCenteredParent_iff] at hx hx'
  have h1 := hx i
  have h2 := hx' i
  rw [hcentre R hR] at h1
  rw [hcentre R' hR'] at h2
  rw [hside] at h1 h2
  have habs : |(R'.index i : ℝ) * (3 : ℝ) ^ source -
      (R.index i : ℝ) * (3 : ℝ) ^ source| <
      (3 : ℝ) ^ source * (3 : ℝ) ^ N := by
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hfactor : |(R'.index i : ℝ) * (3 : ℝ) ^ source -
      (R.index i : ℝ) * (3 : ℝ) ^ source| =
      |(R'.index i : ℝ) - (R.index i : ℝ)| * (3 : ℝ) ^ source := by
    rw [← sub_mul, abs_mul, abs_of_pos hpos]
  rw [hfactor] at habs
  nlinarith [hgeR, hpos]

/-! ## The multiplicity bound -/

/-- **Bounded multiplicity.**  The centred parents of the retained source
cells cover the ambient cube with multiplicity at most `(3 ^ N) ^ d`. -/
theorem sum_setLIntegral_oneStepCenteredParent_le
    {K source : ℤ} {N : ℕ} (f : Vec d → ℝ≥0∞) :
    ∑ R ∈ oneStepRetainedSourceCells (d := d) K source N,
        ∫⁻ x in oneStepCenteredParent (cubeCenter R) (source + (N : ℤ)),
          f x ∂volume ≤
      ((((3 : ℕ) ^ N) ^ d : ℕ) : ℝ≥0∞) *
        ∫⁻ x in cubeSet (originCube d K), f x ∂volume := by
  classical
  haveI : NeZero ((3 : ℕ) ^ N) := ⟨by positivity⟩
  set s : Finset (TriadicCube d) :=
    oneStepRetainedSourceCells (d := d) K source N with hs
  set cls : TriadicCube d → (Fin d → ZMod ((3 : ℕ) ^ N)) :=
    fun R i ↦ ((R.index i : ℤ) : ZMod ((3 : ℕ) ^ N)) with hcls
  have hscale : ∀ R ∈ s, R.scale = source := by
    intro R hR
    exact scale_eq_of_mem_descendantsAtScale
      (mem_oneStepRetainedSourceCells_iff.mp hR).1
  have hsub : ∀ R ∈ s,
      oneStepCenteredParent (cubeCenter R) (source + (N : ℤ)) ⊆
        cubeSet (originCube d K) := by
    intro R hR
    exact ((mem_oneStepRetainedSourceCells_iff.mp hR).2).trans
      (openCubeSet_subset_cubeSet _)
  have hclass : ∀ b : Fin d → ZMod ((3 : ℕ) ^ N),
      ∑ R ∈ s.filter (fun R ↦ cls R = b),
          ∫⁻ x in oneStepCenteredParent (cubeCenter R) (source + (N : ℤ)),
            f x ∂volume ≤
        ∫⁻ x in cubeSet (originCube d K), f x ∂volume := by
    intro b
    have hdisj : Set.PairwiseDisjoint
        ((s.filter (fun R ↦ cls R = b) : Finset (TriadicCube d)) :
          Set (TriadicCube d))
        (fun R ↦ oneStepCenteredParent (cubeCenter R)
          (source + (N : ℤ))) := by
      intro R hR R' hR' hne
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hR hR'
      refine disjoint_oneStepCenteredParent_of_index_modEq
        (hscale R hR.1) (hscale R' hR'.1) hne ?_
      intro i
      have hb : cls R i = cls R' i := by rw [hR.2, hR'.2]
      have := (ZMod.intCast_eq_intCast_iff _ _ _).mp hb
      simpa only [Int.natCast_pow, Nat.cast_ofNat] using this
    have hmeas : ∀ R ∈ s.filter (fun R ↦ cls R = b),
        MeasurableSet (oneStepCenteredParent (cubeCenter R)
          (source + (N : ℤ))) := fun R _ ↦
      measurableSet_oneStepCenteredParent _ _
    rw [← lintegral_biUnion_finset hdisj hmeas f]
    apply lintegral_mono_set
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨R, hR, hxR⟩ := hx
    exact hsub R (Finset.mem_filter.mp hR).1 hxR
  calc
    ∑ R ∈ s, ∫⁻ x in oneStepCenteredParent (cubeCenter R)
          (source + (N : ℤ)), f x ∂volume
        = ∑ b : Fin d → ZMod ((3 : ℕ) ^ N),
          ∑ R ∈ s.filter (fun R ↦ cls R = b),
            ∫⁻ x in oneStepCenteredParent (cubeCenter R)
              (source + (N : ℤ)), f x ∂volume :=
      (Finset.sum_fiberwise s cls _).symm
    _ ≤ ∑ _b : Fin d → ZMod ((3 : ℕ) ^ N),
          ∫⁻ x in cubeSet (originCube d K), f x ∂volume :=
      Finset.sum_le_sum fun b _ ↦ hclass b
    _ = ((Fintype.card (Fin d → ZMod ((3 : ℕ) ^ N)) : ℕ) : ℝ≥0∞) *
          ∫⁻ x in cubeSet (originCube d K), f x ∂volume := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((((3 : ℕ) ^ N) ^ d : ℕ) : ℝ≥0∞) *
          ∫⁻ x in cubeSet (originCube d K), f x ∂volume := by
      congr 2
      simp [ZMod.card]

/-! ## The normalized form -/

/-- The centred parent of a cell, as an `axisCube`. -/
theorem axisCube_centeredParent_eq (R : TriadicCube d) (m : ℤ) :
    axisCube (oneStepCenteredAxisCorner (cubeCenter R) m)
        (cubeScaleFactor (originCube d m)) =
      oneStepCenteredParent (cubeCenter R) m :=
  (translateSet_openCubeSet_originCube_eq_axisCube _ _).symm

/-- `lintegral` against the normalized measure of a centred parent. -/
theorem lintegral_axisCubeNormalizedMeasure_centeredParent
    (R : TriadicCube d) (m : ℤ) (f : Vec d → ℝ≥0∞) :
    ∫⁻ x, f x ∂(CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner (cubeCenter R) m)
        (cubeScaleFactor (originCube d m))) =
      ENNReal.ofReal (((cubeScaleFactor (originCube d m)) ^ d)⁻¹) *
        ∫⁻ x in oneStepCenteredParent (cubeCenter R) m, f x ∂volume := by
  have hL : (0 : ℝ) < cubeScaleFactor (originCube d m) := by
    simpa [cubeScaleFactor] using
      (zpow_pos (by norm_num : (0 : ℝ) < 3) m)
  rw [CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
    _ _ hL, lintegral_smul_measure, axisCube_centeredParent_eq]
  simp only [smul_eq_mul]

/-- **Normalized multiplicity bound.**  With the *full source-cell*
normalization the constant is exactly one, uniformly in `K` and `N`. -/
theorem average_lintegral_centeredParent_le
    {K source : ℤ} {N c : ℕ} (hsource : source ≤ K)
    (hc : ((3 ^ d) ^ ((K - source).toNat) : ℕ) ≤ c)
    (f : Vec d → ℝ≥0∞) :
    ((c : ℝ≥0∞))⁻¹ *
        ∑ R ∈ oneStepRetainedSourceCells (d := d) K source N,
          ∫⁻ x, f x ∂(CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
            (cubeScaleFactor (originCube d (source + (N : ℤ))))) ≤
      ∫⁻ x, f x ∂(normalizedCubeMeasure (originCube d K)) := by
  have hLpos : (0 : ℝ) < cubeScaleFactor (originCube d (source + (N : ℤ))) := by
    simpa [cubeScaleFactor] using
      (zpow_pos (by norm_num : (0 : ℝ) < 3) (source + (N : ℤ)))
  have hbase : (0 : ℝ) < ((3 : ℕ) ^ d : ℕ) := by positivity
  set n₀ : ℕ := (K - source).toNat with hn₀
  set L : ℝ := cubeScaleFactor (originCube d (source + (N : ℤ))) with hL
  -- the numerical constant collapses to the ambient normalization
  have hconst : (((3 ^ d) ^ n₀ : ℕ) : ℝ≥0∞)⁻¹ *
      ENNReal.ofReal ((L ^ d)⁻¹) * ((((3 : ℕ) ^ N) ^ d : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal ((cubeVolume (originCube d K))⁻¹) := by
    have hn₀cast : ((n₀ : ℕ) : ℤ) = K - source := by
      rw [hn₀]; omega
    have hone : (((3 ^ d) ^ n₀ : ℕ) : ℝ≥0∞)⁻¹ =
        ENNReal.ofReal ((((3 ^ d) ^ n₀ : ℕ) : ℝ)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
    have htwo : ((((3 : ℕ) ^ N) ^ d : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal ((((3 : ℕ) ^ N) ^ d : ℕ) : ℝ) :=
      (ENNReal.ofReal_natCast _).symm
    rw [hone, htwo, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hLval : L = (3 : ℝ) ^ (source + (N : ℤ)) := rfl
    have hQval : cubeVolume (originCube d K) = ((3 : ℝ) ^ K) ^ d := rfl
    have hA : ((((3 : ℕ) ^ d) ^ n₀ : ℕ) : ℝ) =
        ((3 : ℝ) ^ (K - source)) ^ d := by
      push_cast
      rw [← pow_mul, mul_comm d n₀, pow_mul, ← zpow_natCast (3 : ℝ) n₀,
        hn₀cast]
    have hB : ((((3 : ℕ) ^ N) ^ d : ℕ) : ℝ) = ((3 : ℝ) ^ (N : ℤ)) ^ d := by
      push_cast
      rw [← zpow_natCast (3 : ℝ) N]
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have hpow : ∀ a : ℤ, ((3 : ℝ) ^ a) ^ d = (3 : ℝ) ^ (a * (d : ℤ)) := by
      intro a
      rw [← zpow_natCast ((3 : ℝ) ^ a) d, ← zpow_mul]
    rw [hA, hB, hLval, hQval]
    simp only [hpow, ← zpow_neg]
    rw [← zpow_add₀ h3, ← zpow_add₀ h3]
    congr 1
    ring
  have hsum : ∑ R ∈ oneStepRetainedSourceCells (d := d) K source N,
      ∫⁻ x, f x ∂(CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
        (cubeScaleFactor (originCube d (source + (N : ℤ))))) =
      ENNReal.ofReal ((L ^ d)⁻¹) *
        ∑ R ∈ oneStepRetainedSourceCells (d := d) K source N,
          ∫⁻ x in oneStepCenteredParent (cubeCenter R)
            (source + (N : ℤ)), f x ∂volume := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun R _ ↦
      lintegral_axisCubeNormalizedMeasure_centeredParent R _ f
  calc
    ((c : ℝ≥0∞))⁻¹ *
        ∑ R ∈ oneStepRetainedSourceCells (d := d) K source N,
          ∫⁻ x, f x ∂(CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
            (cubeScaleFactor (originCube d (source + (N : ℤ)))))
        = ((c : ℝ≥0∞))⁻¹ * (ENNReal.ofReal ((L ^ d)⁻¹) *
            ∑ R ∈ oneStepRetainedSourceCells (d := d) K source N,
              ∫⁻ x in oneStepCenteredParent (cubeCenter R)
                (source + (N : ℤ)), f x ∂volume) := by rw [hsum]
    _ ≤ ((((3 ^ d) ^ n₀ : ℕ) : ℝ≥0∞))⁻¹ * (ENNReal.ofReal ((L ^ d)⁻¹) *
            ((((3 : ℕ) ^ N) ^ d : ℕ) : ℝ≥0∞) *
              ∫⁻ x in cubeSet (originCube d K), f x ∂volume) := by
          have hcard : ((c : ℝ≥0∞))⁻¹ ≤ ((((3 ^ d) ^ n₀ : ℕ) : ℝ≥0∞))⁻¹ := by
            apply ENNReal.inv_le_inv.mpr
            exact_mod_cast hc
          refine mul_le_mul' hcard ?_
          rw [mul_assoc]
          exact mul_le_mul' le_rfl
            (sum_setLIntegral_oneStepCenteredParent_le f)
    _ = (((((3 ^ d) ^ n₀ : ℕ) : ℝ≥0∞))⁻¹ * ENNReal.ofReal ((L ^ d)⁻¹) *
            ((((3 : ℕ) ^ N) ^ d : ℕ) : ℝ≥0∞)) *
              ∫⁻ x in cubeSet (originCube d K), f x ∂volume := by ring
    _ = ENNReal.ofReal ((cubeVolume (originCube d K))⁻¹) *
          ∫⁻ x in cubeSet (originCube d K), f x ∂volume := by rw [hconst]
    _ = ∫⁻ x, f x ∂(normalizedCubeMeasure (originCube d K)) :=
      (lintegral_normalizedCubeMeasure_eq _ f).symm

/-! ## Probability normalization and the `eLpNorm` form -/

/-- Lebesgue volume of an axis cube. -/
theorem volume_axisCube_eq (z : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    volume (axisCube z L) = ENNReal.ofReal (L ^ d) := by
  rw [axisCube, volume_pi_pi]
  simp only [Real.volume_Ioo, add_sub_cancel_left]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hL]

instance isProbabilityMeasure_axisCubeNormalizedMeasure
    (z : Vec d) {L : ℝ} (hL : 0 < L) :
    IsProbabilityMeasure
      (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) := by
  constructor
  rw [CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
    z L hL, Measure.smul_apply, Measure.restrict_apply_univ,
    volume_axisCube_eq z hL.le, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  rw [inv_mul_cancel₀ (by positivity : (L : ℝ) ^ d ≠ 0), ENNReal.ofReal_one]

/-- The normalized measure of a retained cell's centred parent is dominated by
a finite multiple of the ambient normalized cube measure. -/
theorem axisCubeNormalizedMeasure_centeredParent_le_smul
    {K source : ℤ} {N : ℕ} {R : TriadicCube d}
    (hR : R ∈ oneStepRetainedSourceCells (d := d) K source N) :
    CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
        (cubeScaleFactor (originCube d (source + (N : ℤ)))) ≤
      ENNReal.ofReal (cubeVolume (originCube d K) /
          (cubeScaleFactor (originCube d (source + (N : ℤ)))) ^ d) •
        normalizedCubeMeasure (originCube d K) := by
  have hLpos : (0 : ℝ) < cubeScaleFactor (originCube d (source + (N : ℤ))) := by
    simpa [cubeScaleFactor] using
      (zpow_pos (by norm_num : (0 : ℝ) < 3) (source + (N : ℤ)))
  have hQpos : (0 : ℝ) < cubeVolume (originCube d K) :=
    cubeVolume_pos _
  set L : ℝ := cubeScaleFactor (originCube d (source + (N : ℤ))) with hL
  have hsub : axisCube (oneStepCenteredAxisCorner (cubeCenter R)
      (source + (N : ℤ))) L ⊆ cubeSet (originCube d K) := by
    rw [axisCube_centeredParent_eq]
    exact ((mem_oneStepRetainedSourceCells_iff.mp hR).2).trans
      (openCubeSet_subset_cubeSet _)
  have hconst : ENNReal.ofReal (cubeVolume (originCube d K) / L ^ d) *
      ENNReal.ofReal ((cubeVolume (originCube d K))⁻¹) =
      ENNReal.ofReal ((L ^ d)⁻¹) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
    _ _ hLpos, normalizedCubeMeasure, cubeMeasure, smul_smul, hconst]
  refine Measure.le_iff.2 fun A hA ↦ ?_
  simp only [Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  gcongr

/-- **Normalized `L²`-to-`L⁴` multiplicity bound over the retained source
cells.**  Exact analogue of
`overlapCentersAtDepth_average_eLpNorm_two_rpow_four_le`, with constant one. -/
theorem average_eLpNorm_two_rpow_four_centeredParent_le
    {K source : ℤ} {N c : ℕ} (hsource : source ≤ K)
    (hc : ((3 ^ d) ^ ((K - source).toNat) : ℕ) ≤ c)
    (f : Vec d → HilbertVec d)
    (hf : MemLp f 4 (normalizedCubeMeasure (originCube d K))) :
    ((c : ℝ≥0∞))⁻¹ *
        ∑ R ∈ oneStepRetainedSourceCells (d := d) K source N,
          (eLpNorm f 2 (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
            (cubeScaleFactor
              (originCube d (source + (N : ℤ)))))) ^ (4 : ℝ) ≤
      (eLpNorm f 4 (normalizedCubeMeasure (originCube d K))) ^ (4 : ℝ) := by
  have hLpos : (0 : ℝ) < cubeScaleFactor (originCube d (source + (N : ℤ))) := by
    simpa [cubeScaleFactor] using
      (zpow_pos (by norm_num : (0 : ℝ) < 3) (source + (N : ℤ)))
  have hlocal : ∀ R ∈ oneStepRetainedSourceCells (d := d) K source N,
      (eLpNorm f 2 (CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
        (cubeScaleFactor
          (originCube d (source + (N : ℤ)))))) ^ (4 : ℝ) ≤
        ∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ)
          ∂(CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
            (cubeScaleFactor (originCube d (source + (N : ℤ))))) := by
    intro R hR
    letI : IsProbabilityMeasure
        (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
          (cubeScaleFactor (originCube d (source + (N : ℤ))))) :=
      isProbabilityMeasure_axisCubeNormalizedMeasure _ hLpos
    have hfR : MemLp f 4
        (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
          (cubeScaleFactor (originCube d (source + (N : ℤ))))) :=
      MemLp.of_measure_le_smul (c := ENNReal.ofReal
          (cubeVolume (originCube d K) /
            (cubeScaleFactor (originCube d (source + (N : ℤ)))) ^ d))
        ENNReal.ofReal_ne_top
        (axisCubeNormalizedMeasure_centeredParent_le_smul hR) hf
    have hnorm := eLpNorm_le_eLpNorm_of_exponent_le
      (μ := CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
        (cubeScaleFactor (originCube d (source + (N : ℤ)))))
      (p := 2) (q := 4) (by norm_num) hfR.1
    calc
      _ ≤ (eLpNorm f 4 (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
            (cubeScaleFactor
              (originCube d (source + (N : ℤ)))))) ^ (4 : ℝ) :=
        ENNReal.rpow_le_rpow hnorm (by norm_num)
      _ = _ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
        norm_num only [ENNReal.toReal_ofNat]
        rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
          ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)]
  calc
    _ ≤ ((c : ℝ≥0∞))⁻¹ *
        ∑ R ∈ oneStepRetainedSourceCells (d := d) K source N,
          ∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ)
            ∂(CubeCalderonZygmund.axisCubeNormalizedMeasure
              (oneStepCenteredAxisCorner (cubeCenter R) (source + (N : ℤ)))
              (cubeScaleFactor (originCube d (source + (N : ℤ))))) := by
      gcongr with R hR
      exact hlocal R hR
    _ ≤ ∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂(normalizedCubeMeasure (originCube d K)) :=
      average_lintegral_centeredParent_le hsource hc _
    _ = (eLpNorm f 4 (normalizedCubeMeasure (originCube d K))) ^ (4 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
      norm_num only [ENNReal.toReal_ofNat]
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
        ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
