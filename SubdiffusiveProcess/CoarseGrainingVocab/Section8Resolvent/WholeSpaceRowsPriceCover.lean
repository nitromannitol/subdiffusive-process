
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellUniform

@[expose] public section

/-!
# The price leg of the coarse contraction: a triadic cover of the cutoff support

the intermediate-ball geometry corrected the pairing of the two mesoscopic inputs of
`massive_local_l2_coarse_contraction_of_energy_price_on`: the coarse energy
bound can only be produced on a pair `V ⊊ W`, so the price has to be produced on
the *same* `V`, namely the ball `Metric.ball c ((4/5) 3^n)` which contains the
support of the cutoff `exists_smooth_translatedCube_cutoff_ball`.

price summation is stated on the triadic descendants of a triadic cube,
which cannot be used here because the contraction cube `translatedCube d (n+1) c`
is an arbitrary translate.  A change of variables is **not needed**: the price, unlike the coarse energy
bound, needs no Caccioppoli core and therefore no half-grid translation
(the splitting argument), so its cells may be *genuine* triadic cubes at scale `k`, whose grid
is fixed and independent of `c`.  The grid misalignment costs at most one cell of
slack per side, which is affordable because the mesoscopic scale `k` is far below
the contraction scale `n`.

That is what this file does.

* §1 the triadic price cells at scale `k`, their rounding index, and the finite
  index box of the cells that meet the closed box of half-width `rho` about `c`;
* §2 the three geometric facts: the cells cover that closed box, they are
  pairwise disjoint, and (when `rho + 3^k < rho1`) they lie inside
  `Metric.ball c rho1`;
* §3 the three integral hypotheses of `mesoscopicCrossPriceEnergyOn_of_cells`
  and `mesoscopicCrossPriceEnergyOn_ball_of_triadicCells`, the price on
  `(ball, ball)`;
* §4 `mesoscopicCrossPriceEnergyOn_contraction_pair_of_triadicCells`, the price
  on the pair `(translatedCube d (n+1) c, ball)` that the contraction consumes,
  by `mesoscopicCrossPriceEnergyOn_of_subdomain`.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## 1. The triadic price cells -/

/-- The genuine triadic cube at scale `k` with index `m`.  Unlike the
mesoscopic energy cells `mesoCell`, these are not translated: the price needs no
Caccioppoli core, so it can be run on the fixed triadic grid. -/
def priceCell (d : ℕ) (k : ℤ) (m : Fin d → ℤ) : TriadicCube d :=
  { scale := k, index := m }

@[simp] theorem cubeScaleFactor_priceCell (k : ℤ) (m : Fin d → ℤ) :
    cubeScaleFactor (priceCell d k m) = (3 : ℝ) ^ k := rfl

theorem mem_cubeSet_priceCell_iff {k : ℤ} {m : Fin d → ℤ} {x : Vec d} :
    x ∈ cubeSet (priceCell d k m) ↔
      ∀ i, ((m i : ℝ) - 1 / 2) * (3 : ℝ) ^ k ≤ x i ∧
        x i < ((m i : ℝ) + 1 / 2) * (3 : ℝ) ^ k :=
  Iff.rfl

theorem openCubeSet_priceCell_subset (k : ℤ) (m : Fin d → ℤ) :
    openCubeSet (priceCell d k m) ⊆ cubeSet (priceCell d k m) := by
  intro x hx
  exact fun i => ⟨le_of_lt (hx i).1, (hx i).2⟩

/-- The index of the unique scale-`k` triadic cell containing a point. -/
def priceRoundIndex (d : ℕ) (k : ℤ) (x : Vec d) : Fin d → ℤ :=
  fun i => ⌊x i / (3 : ℝ) ^ k + 1 / 2⌋

theorem mem_cubeSet_priceRoundIndex (k : ℤ) (x : Vec d) :
    x ∈ cubeSet (priceCell d k (priceRoundIndex d k x)) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [mem_cubeSet_priceCell_iff]
  intro i
  have hfl := Int.floor_le (x i / (3 : ℝ) ^ k + 1 / 2)
  have hlt := Int.lt_floor_add_one (x i / (3 : ℝ) ^ k + 1 / 2)
  have hcancel : x i / (3 : ℝ) ^ k * (3 : ℝ) ^ k = x i :=
    div_mul_cancel₀ _ (ne_of_gt h3)
  have h4 : ((⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ : ℤ) : ℝ) * (3 : ℝ) ^ k ≤
      x i + 1 / 2 * (3 : ℝ) ^ k := by
    have hmul := mul_le_mul_of_nonneg_right hfl h3.le
    rw [add_mul, hcancel] at hmul
    linarith only [hmul]
  have h5 : x i + 1 / 2 * (3 : ℝ) ^ k <
      ((⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ : ℤ) : ℝ) * (3 : ℝ) ^ k + (3 : ℝ) ^ k := by
    have hmul := mul_lt_mul_of_pos_right hlt h3
    rw [add_mul, hcancel, add_mul, one_mul] at hmul
    linarith only [hmul]
  simp only [priceRoundIndex]
  constructor
  · rw [sub_mul]
    linarith only [h4]
  · rw [add_mul]
    linarith only [h5]

/-- The finite family of scale-`k` triadic indices whose cells meet the closed
box of half-width `rho` about `c`. -/
def priceIndexBox (d : ℕ) (k : ℤ) (c : Vec d) (rho : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i : Fin d =>
    Finset.Icc ⌈(c i - rho) / (3 : ℝ) ^ k - 1 / 2⌉
      ⌊(c i + rho) / (3 : ℝ) ^ k + 1 / 2⌋

/-! ## 2. Cover, disjointness, containment -/

/-- **The cells cover the closed box.**  Every point of the closed box of
half-width `rho` about `c` lies in the cell of its rounding index, and that
index belongs to the box. -/
theorem priceRoundIndex_mem_priceIndexBox {k : ℤ} {c : Vec d} {rho : ℝ}
    {x : Vec d} (hx : ∀ i, |x i - c i| ≤ rho) :
    priceRoundIndex d k x ∈ priceIndexBox d k c rho := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [priceIndexBox, Fintype.mem_piFinset]
  intro i
  have hfl := Int.floor_le (x i / (3 : ℝ) ^ k + 1 / 2)
  have hlt := Int.lt_floor_add_one (x i / (3 : ℝ) ^ k + 1 / 2)
  have habs := abs_le.1 (hx i)
  refine Finset.mem_Icc.2 ⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩
  · simp only [priceRoundIndex]
    have hmono : (c i - rho) / (3 : ℝ) ^ k ≤ x i / (3 : ℝ) ^ k := by
      gcongr
      linarith only [habs.1]
    linarith only [hmono, hlt]
  · simp only [priceRoundIndex]
    have hmono : x i / (3 : ℝ) ^ k ≤ (c i + rho) / (3 : ℝ) ^ k := by
      gcongr
      linarith only [habs.2]
    linarith only [hmono, hfl]

/-- **Containment.**  If the slack `3^k` of the grid misalignment still fits
inside the larger radius, every cell of the index box lies in the ball. -/
theorem cubeSet_priceCell_subset_ball {k : ℤ} {c : Vec d} {rho rho1 : ℝ}
    (hrho1 : 0 < rho1) (hslack : rho + (3 : ℝ) ^ k < rho1)
    {m : Fin d → ℤ} (hm : m ∈ priceIndexBox d k c rho) :
    cubeSet (priceCell d k m) ⊆ Metric.ball c rho1 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [priceIndexBox, Fintype.mem_piFinset] at hm
  intro x hx
  rw [mem_ball_iff_abs hrho1]
  intro i
  have hi := Finset.mem_Icc.1 (hm i)
  have hlo : ((⌈(c i - rho) / (3 : ℝ) ^ k - 1 / 2⌉ : ℤ) : ℝ) ≤ (m i : ℝ) := by
    exact_mod_cast hi.1
  have hhi : ((m i : ℤ) : ℝ) ≤ ((⌊(c i + rho) / (3 : ℝ) ^ k + 1 / 2⌋ : ℤ) : ℝ) := by
    exact_mod_cast hi.2
  have hlo' : (c i - rho) / (3 : ℝ) ^ k - 1 / 2 ≤ (m i : ℝ) :=
    le_trans (Int.le_ceil _) hlo
  have hhi' : (m i : ℝ) ≤ (c i + rho) / (3 : ℝ) ^ k + 1 / 2 :=
    le_trans hhi (Int.floor_le _)
  have hcell := (mem_cubeSet_priceCell_iff.1 hx) i
  have hA : c i - rho - (3 : ℝ) ^ k / 2 ≤ (m i : ℝ) * (3 : ℝ) ^ k := by
    have := (div_le_iff₀ h3).1 (by linarith only [hlo'] :
      (c i - rho) / (3 : ℝ) ^ k ≤ (m i : ℝ) + 1 / 2)
    linarith only [this]
  have hB : (m i : ℝ) * (3 : ℝ) ^ k ≤ c i + rho + (3 : ℝ) ^ k / 2 := by
    have := (le_div_iff₀ h3).1 (by linarith only [hhi'] :
      (m i : ℝ) - 1 / 2 ≤ (c i + rho) / (3 : ℝ) ^ k)
    linarith only [this]
  rw [abs_lt]
  constructor
  · nlinarith [hcell.1, hA, h3]
  · nlinarith [hcell.2, hB, h3]

/-- **The triadic grid at a fixed scale is injective on points.** -/
theorem eq_of_mem_cubeSet_priceCell {k : ℤ} {m m' : Fin d → ℤ} {x : Vec d}
    (h1 : x ∈ cubeSet (priceCell d k m)) (h2 : x ∈ cubeSet (priceCell d k m')) :
    m = m' := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  funext i
  have hA := (mem_cubeSet_priceCell_iff.1 h1) i
  have hB := (mem_cubeSet_priceCell_iff.1 h2) i
  have hlt : |((m i : ℝ)) - ((m' i : ℝ))| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2, h3]
  have hint : |(m i : ℤ) - (m' i : ℤ)| < 1 := by
    have hcast : |((m i - m' i : ℤ) : ℝ)| < 1 := by push_cast; exact hlt
    exact_mod_cast hcast
  have := abs_lt.1 hint
  omega

/-- **Disjointness.**  Distinct scale-`k` triadic cells are disjoint. -/
theorem disjoint_cubeSet_priceCell {k : ℤ} {m m' : Fin d → ℤ} (h : m ≠ m') :
    Disjoint (cubeSet (priceCell d k m)) (cubeSet (priceCell d k m')) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact h (eq_of_mem_cubeSet_priceCell hx hx')

/-- **Multiplicity one.**  At most one scale-`k` triadic cell contains a given
point. -/
theorem card_filter_mem_openCubeSet_priceCell_le (k : ℤ) (F : Finset (Fin d → ℤ))
    (x : Vec d) :
    ((F.filter fun m => x ∈ openCubeSet (priceCell d k m)).card : ℝ) ≤ 1 := by
  classical
  have hcard : (F.filter fun m => x ∈ openCubeSet (priceCell d k m)).card ≤ 1 := by
    refine Finset.card_le_one.2 ?_
    intro m hm m' hm'
    rw [Finset.mem_filter] at hm hm'
    exact eq_of_mem_cubeSet_priceCell (openCubeSet_priceCell_subset k m hm.2)
      (openCubeSet_priceCell_subset k m' hm'.2)
  exact_mod_cast hcard

/-! ## 3. The price on the intermediate ball -/

/-- The union of the cells of the index box. -/
def priceCover (d : ℕ) (k : ℤ) (c : Vec d) (rho : ℝ) : Set (Vec d) :=
  ⋃ m ∈ priceIndexBox d k c rho, cubeSet (priceCell d k m)

theorem measurableSet_priceCover (d : ℕ) (k : ℤ) (c : Vec d) (rho : ℝ) :
    MeasurableSet (priceCover d k c rho) := by
  classical
  refine Set.Finite.measurableSet_biUnion ?_ fun m _ => measurableSet_cubeSet _
  exact (priceIndexBox d k c rho).finite_toSet

theorem priceCover_subset_ball {k : ℤ} {c : Vec d} {rho rho1 : ℝ}
    (hrho1 : 0 < rho1) (hslack : rho + (3 : ℝ) ^ k < rho1) :
    priceCover d k c rho ⊆ Metric.ball c rho1 := by
  refine Set.iUnion₂_subset fun m hm => ?_
  exact cubeSet_priceCell_subset_ball hrho1 hslack hm

theorem mem_priceCover_of_abs_le {k : ℤ} {c : Vec d} {rho : ℝ} {x : Vec d}
    (hx : ∀ i, |x i - c i| ≤ rho) : x ∈ priceCover d k c rho := by
  refine Set.mem_iUnion₂.2 ⟨priceRoundIndex d k x, ?_, ?_⟩
  · exact priceRoundIndex_mem_priceIndexBox hx
  · exact mem_cubeSet_priceRoundIndex k x

/-- **The cross integral does not see the complement of the cover.**

The integrand of the mesoscopic cross term carries the factor `chi`, so it
vanishes off `tsupport chi`; and `tsupport chi` is inside the closed box of
half-width `rho`, which the cells of the index box cover. -/
theorem setIntegral_cross_eq_priceCover {a w chi : Vec d → ℝ}
    {G : Vec d → Vec d} {k : ℤ} {c : Vec d} {rho : ℝ} {S : Set (Vec d)}
    (hSmeas : MeasurableSet S) (hSsub : priceCover d k c rho ⊆ S)
    (hsupp : tsupport chi ⊆ {x : Vec d | ∀ i, |x i - c i| ≤ rho}) :
    (∫ x in S, a x * chi x * w x *
        vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume) =
      ∫ x in priceCover d k c rho, a x * chi x * w x *
        vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume := by
  classical
  set F : Vec d → ℝ := fun x => a x * chi x * w x *
    vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) with hF
  have hUmeas : MeasurableSet (priceCover d k c rho) :=
    measurableSet_priceCover d k c rho
  have hzero : ∀ x, x ∉ priceCover d k c rho → F x = 0 := by
    intro x hx
    have hts : x ∉ tsupport chi := fun hmem =>
      hx (mem_priceCover_of_abs_le (hsupp hmem))
    have hchi : chi x = 0 :=
      Function.notMem_support.1 fun hmem => hts (subset_tsupport chi hmem)
    simp [hF, hchi]
  have hind : S.indicator F = (priceCover d k c rho).indicator F := by
    funext x
    by_cases hU : x ∈ priceCover d k c rho
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem (hSsub hU)]
    · rw [Set.indicator_of_notMem hU]
      by_cases hb : x ∈ S
      · rw [Set.indicator_of_mem hb, hzero x hU]
      · rw [Set.indicator_of_notMem hb]
  rw [← integral_indicator hSmeas, hind, integral_indicator hUmeas]

/-- **The mesoscopic price on the intermediate ball, from the per-cell prices on
the triadic grid.**

`mesoscopicCrossPriceEnergyOn_of_cells` with `Ws = Vs = openCubeSet` of the
scale-`k` triadic cells that meet the closed box of half-width `rho`: the cross
term splits exactly because the integrand carries the cutoff and the cells cover
its support, and the energy and mass sums are bounded by the ball integrals with
multiplicity one because the cells are disjoint and lie inside the ball. -/
theorem mesoscopicCrossPriceEnergyOn_ball_of_triadicCells
    {a w chi : Vec d → ℝ} {G : Vec d → Vec d} {t P R Sc : ℝ}
    {k : ℤ} {c : Vec d} {rho rho1 : ℝ}
    (ht : 0 < t) (hP : 0 ≤ P) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hrho1 : 0 < rho1) (hslack : rho + (3 : ℝ) ^ k < rho1)
    (haNonneg : ∀ x, 0 ≤ a x)
    (hsupp : tsupport chi ⊆ {x : Vec d | ∀ i, |x i - c i| ≤ rho})
    (hcrossInt : IntegrableOn (fun x => a x * chi x * w x *
      vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (Metric.ball c rho1) volume)
    (henergyInt : IntegrableOn (fun x => a x * vecNormSq (G x))
      (Metric.ball c rho1) volume)
    (hmassInt : IntegrableOn (fun x => w x ^ 2) (Metric.ball c rho1) volume)
    (hcell : ∀ m ∈ priceIndexBox d k c rho,
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) w G chi t P R Sc) :
    MesoscopicCrossPriceEnergyOn a (Metric.ball c rho1) (Metric.ball c rho1)
      w G chi t P R Sc := by
  classical
  set I : Finset (Fin d → ℤ) := priceIndexBox d k c rho with hI
  have hBmeas : MeasurableSet (Metric.ball c rho1) := measurableSet_ball
  have hsubClosed : ∀ m ∈ I, cubeSet (priceCell d k m) ⊆ Metric.ball c rho1 :=
    fun m hm => cubeSet_priceCell_subset_ball hrho1 hslack hm
  have hsubOpen : ∀ m ∈ I, openCubeSet (priceCell d k m) ⊆ Metric.ball c rho1 :=
    fun m hm => (openCubeSet_priceCell_subset k m).trans (hsubClosed m hm)
  have hdisj : Set.Pairwise (↑I : Set (Fin d → ℤ))
      (Function.onFun Disjoint fun m => cubeSet (priceCell d k m)) :=
    fun m _ m' _ h => disjoint_cubeSet_priceCell h
  refine mesoscopicCrossPriceEnergyOn_of_cells I
    (Ws := fun m => openCubeSet (priceCell d k m))
    (Vs := fun m => openCubeSet (priceCell d k m))
    ht hP hR hSc ?_ ?_ hcell ?_ ?_ ?_
  · intro m
    exact setIntegral_nonneg (measurableSet_openCubeSet _) fun x _ =>
      mul_nonneg (haNonneg x) (vecNormSq_nonneg _)
  · intro m
    exact setIntegral_nonneg (measurableSet_openCubeSet _) fun x _ => sq_nonneg _
  · have hstep1 := setIntegral_cross_eq_priceCover (a := a) (w := w) (chi := chi)
      (G := G) (k := k) (c := c) (rho := rho) hBmeas
      (priceCover_subset_ball hrho1 hslack) hsupp
    have hstep2 : (∫ x in priceCover d k c rho, a x * chi x * w x *
          vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume) =
        ∑ m ∈ I, ∫ x in cubeSet (priceCell d k m), a x * chi x * w x *
          vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume := by
      rw [priceCover]
      exact integral_biUnion_finset I (fun m _ => measurableSet_cubeSet _) hdisj
        fun m hm => hcrossInt.mono_set (hsubClosed m hm)
    have hstep3 : ∀ m ∈ I,
        (∫ x in cubeSet (priceCell d k m), a x * chi x * w x *
          vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume) =
        ∫ x in openCubeSet (priceCell d k m), a x * chi x * w x *
          vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume :=
      fun m _ => setIntegral_cubeSet_eq_setIntegral_openCubeSet
    rw [hstep1, hstep2, Finset.sum_congr rfl hstep3, Finset.mul_sum]
  · have := sum_setIntegral_le_of_overlap I
      (A := fun m => openCubeSet (priceCell d k m))
      (fun m => measurableSet_openCubeSet _) hBmeas (N := 1)
      (f := fun x => a x * vecNormSq (G x))
      (fun x => mul_nonneg (haNonneg x) (vecNormSq_nonneg _)) hsubOpen
      (card_filter_mem_openCubeSet_priceCell_le k I) henergyInt
    simpa using this
  · have := sum_setIntegral_le_of_overlap I
      (A := fun m => openCubeSet (priceCell d k m))
      (fun m => measurableSet_openCubeSet _) hBmeas (N := 1)
      (f := fun x => w x ^ 2) (fun x => sq_nonneg _) hsubOpen
      (card_filter_mem_openCubeSet_priceCell_le k I) hmassInt
    simpa using this

/-! ## 4. The pair the contraction consumes -/

/-- **The cutoff of `exists_smooth_translatedCube_cutoff_ball` with its support
recorded as a box.**

Identical data, but the support conclusion is the sharp closed box of half-width
`(3/4) 3^n` produced by `exists_smoothBoxCutoff` with margin `3^n/4`.  The ball
form is the corollary `tsupport_box_subset_ball` below; the box form is what the
price cover of §3 consumes. -/
theorem exists_smooth_translatedCube_cutoff_box (d : ℕ) (n : ℤ) (z : Vec d) :
    ∃ chi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ (∀ x, |chi x| ≤ 1) ∧
      (∀ x ∈ translatedCube d n z, chi x = 1) ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ {x : Vec d | ∀ i, |x i - z i| ≤ 3 / 4 * (3 : ℝ) ^ n} ∧
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
    intro i
    have h1 := hx.1 i
    have h2 := hx.2 i
    simp only [hr_def] at h1 h2
    rw [abs_le]
    constructor <;> linarith only [h1, h2]
  · have hbound := hsq x
    have hcalc : vecNormSq (fun i ↦ (fderiv ℝ eta x) (basisVec i)) =
        ∑ i, ((fderiv ℝ eta x) (Pi.single i 1)) ^ 2 := by
      simp [vecNormSq, vecDot, basisVec, pow_two]
    rw [hcalc]
    refine hbound.trans (le_of_eq ?_)
    have hne : ((3 : ℝ) ^ n) ≠ 0 := ne_of_gt h3
    field_simp
    ring

/-- The closed box of half-width `(3/4) 3^n` sits inside the ball of radius
`(4/5) 3^n`. -/
theorem box_subset_ball (d : ℕ) (n : ℤ) (z : Vec d) :
    {x : Vec d | ∀ i, |x i - z i| ≤ 3 / 4 * (3 : ℝ) ^ n} ⊆
      Metric.ball z (4 / 5 * (3 : ℝ) ^ n) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  intro x hx
  rw [mem_ball_iff_abs (by positivity)]
  intro i
  have := hx i
  linarith only [this, h3]

/-- The mesoscopic slack condition: three triadic scales below the contraction
scale, the grid misalignment of the price cells still fits between the cutoff's
support box and the intermediate ball. -/
theorem price_slack_bound {k n : ℤ} (hkn : k ≤ n - 3) :
    3 / 4 * (3 : ℝ) ^ n + (3 : ℝ) ^ k < 4 / 5 * (3 : ℝ) ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hk : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (n - 3) :=
    zpow_le_zpow_right₀ (by norm_num) hkn
  have hval : (3 : ℝ) ^ (n - 3) = (3 : ℝ) ^ n / 27 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  rw [hval] at hk
  linarith only [hk, h3]

/-- **The mesoscopic price on the pair the coarse contraction consumes.**

`W = translatedCube d (n+1) c` is the contraction denominator and
`V = Metric.ball c ((4/5) 3^n)` the intermediate set of
`coarseEnergyBoundOn_contraction_pair_of_mesoCells`.  The price is produced on
`(V, V)` by §3 and transported to `(W, V)` by
`mesoscopicCrossPriceEnergyOn_of_subdomain`: the mass only grows, and the cross
term is unchanged because both integrals equal the integral over the cover of
the cutoff's support. -/
theorem mesoscopicCrossPriceEnergyOn_contraction_pair_of_triadicCells
    {a w chi : Vec d → ℝ} {G : Vec d → Vec d} {t P R Sc : ℝ}
    {k n : ℤ} {c : Vec d}
    (hkn : k ≤ n - 3) (ht : 0 < t) (hP : 0 ≤ P) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (haNonneg : ∀ x, 0 ≤ a x)
    (hsupp : tsupport chi ⊆ {x : Vec d | ∀ i, |x i - c i| ≤ 3 / 4 * (3 : ℝ) ^ n})
    (hcrossInt : IntegrableOn (fun x => a x * chi x * w x *
      vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (translatedCube d (n + 1) c) volume)
    (henergyInt : IntegrableOn (fun x => a x * vecNormSq (G x))
      (translatedCube d (n + 1) c) volume)
    (hmassInt : IntegrableOn (fun x => w x ^ 2)
      (translatedCube d (n + 1) c) volume)
    (hcell : ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) w G chi t P R Sc) :
    MesoscopicCrossPriceEnergyOn a (translatedCube d (n + 1) c)
      (Metric.ball c (4 / 5 * (3 : ℝ) ^ n)) w G chi t P R Sc := by
  classical
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hrho1 : (0 : ℝ) < 4 / 5 * (3 : ℝ) ^ n := by positivity
  have hslack := price_slack_bound (k := k) (n := n) hkn
  have hballW : Metric.ball c (4 / 5 * (3 : ℝ) ^ n) ⊆ translatedCube d (n + 1) c :=
    ball_subset_translatedCube_succ d n c
  have hWmeas : MeasurableSet (translatedCube d (n + 1) c) :=
    (isOpenBoundedConvexDomain_translatedCube (n + 1) c).isOpen.measurableSet
  have hBmeas : MeasurableSet (Metric.ball c (4 / 5 * (3 : ℝ) ^ n)) :=
    measurableSet_ball
  have hcoverB : priceCover d k c (3 / 4 * (3 : ℝ) ^ n) ⊆
      Metric.ball c (4 / 5 * (3 : ℝ) ^ n) := priceCover_subset_ball hrho1 hslack
  have hbase : MesoscopicCrossPriceEnergyOn a
      (Metric.ball c (4 / 5 * (3 : ℝ) ^ n))
      (Metric.ball c (4 / 5 * (3 : ℝ) ^ n)) w G chi t P R Sc :=
    mesoscopicCrossPriceEnergyOn_ball_of_triadicCells ht hP hR hSc hrho1 hslack
      haNonneg hsupp (hcrossInt.mono_set hballW) (henergyInt.mono_set hballW)
      (hmassInt.mono_set hballW) hcell
  refine mesoscopicCrossPriceEnergyOn_of_subdomain ht hP hR hSc ?_ ?_ hbase
  · exact setIntegral_mono_set hmassInt
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall hballW)
  · rw [setIntegral_cross_eq_priceCover (k := k) hWmeas (hcoverB.trans hballW) hsupp,
      setIntegral_cross_eq_priceCover (k := k) hBmeas hcoverB hsupp]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
