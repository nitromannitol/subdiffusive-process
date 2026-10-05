module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalSmallRadius
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Model.OGammaLE

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## A Dirac measure makes every sigma-algebra independent -/

theorem measure_dirac_bool_pos {s : Set Bool} (h : true ∈ s) :
    (Measure.dirac true) s = 1 :=
  Measure.dirac_apply_of_mem h

theorem measure_dirac_bool_neg {s : Set Bool} (h : true ∉ s) :
    (Measure.dirac true) s = 0 := by
  rw [Measure.dirac_apply' _ (by trivial)]
  simp [h]

theorem dirac_bool_inter (t1 t2 : Set Bool) :
    (Measure.dirac true) (t1 ∩ t2) =
      (Measure.dirac true) t1 * (Measure.dirac true) t2 := by
  by_cases h1 : true ∈ t1
  · by_cases h2 : true ∈ t2
    · rw [measure_dirac_bool_pos (Set.mem_inter h1 h2), measure_dirac_bool_pos h1,
        measure_dirac_bool_pos h2]
      simp
    · rw [measure_dirac_bool_neg (fun hm => h2 hm.2), measure_dirac_bool_neg h2]
      simp
  · rw [measure_dirac_bool_neg (fun hm => h1 hm.1), measure_dirac_bool_neg h1]
    simp

theorem dirac_bool_iInter {ι : Type} (s : Finset ι) (f : ι → Set Bool) :
    (Measure.dirac true) (⋂ i ∈ s, f i) = ∏ i ∈ s, (Measure.dirac true) (f i) := by
  by_cases h : ∀ i ∈ s, true ∈ f i
  · have hmem : true ∈ ⋂ i ∈ s, f i := by
      simp only [Set.mem_iInter]
      exact fun i hi => h i hi
    rw [measure_dirac_bool_pos hmem,
      Finset.prod_congr rfl (fun i hi => measure_dirac_bool_pos (h i hi))]
    simp
  · push Not at h
    obtain ⟨i0, hi0, hnot⟩ := h
    have hfalse : true ∉ ⋂ i ∈ s, f i := by
      simp only [Set.mem_iInter, not_forall]
      exact ⟨i0, hi0, hnot⟩
    rw [measure_dirac_bool_neg hfalse]
    exact (Finset.prod_eq_zero hi0 (measure_dirac_bool_neg hnot)).symm

/-- Under a Dirac measure every pair of sigma-algebras is independent. -/
theorem indep_of_dirac_bool {mu : Measure Bool} (hmu : mu = Measure.dirac true)
    (m1 m2 : MeasurableSpace Bool) : Indep m1 m2 mu := by
  subst hmu
  refine fun t1 t2 _ _ => Filter.Eventually.of_forall fun _ => ?_
  simp only [Kernel.const_apply]
  exact dirac_bool_inter t1 t2

/-- Under a Dirac measure every family of sigma-algebras is independent. -/
theorem iIndep_of_dirac_bool {mu : Measure Bool} (hmu : mu = Measure.dirac true)
    {ι : Type} (m : ι → MeasurableSpace Bool) : iIndep m mu := by
  subst hmu
  refine fun s f _ => Filter.Eventually.of_forall fun _ => ?_
  simp only [Kernel.const_apply]
  exact dirac_bool_iInter s f

/-! ## The degenerate field -/

/-- The event field that occurs only at the null sample `false`. -/
def nullField (d : ℕ) : ℕ → Lattice d → Set Bool := fun _ _ => {false}

theorem measure_nullField (j : ℕ) (z : Lattice d) :
    (Measure.dirac true) (nullField d j z) = 0 := by
  refine measure_dirac_bool_neg ?_
  simp [nullField]

theorem independentEventScales_nullField :
    IndependentEventScales (Measure.dirac true) (nullField d) :=
  iIndep_of_dirac_bool rfl _

theorem multiscaleFiniteRangeIndependentEvents_nullField (R : ℕ → ℕ) :
    MultiscaleFiniteRangeIndependentEvents (Measure.dirac true) R (nullField d) :=
  fun _ _ _ _ => indep_of_dirac_bool rfl _ _

theorem translationInvariantEventLaw_nullField :
    TranslationInvariantEventLaw (Measure.dirac true) (nullField d) :=
  ⟨fun _ _ => trivial, fun _ => rfl⟩

/-- At the null sample, no site is percolation-good. -/
theorem not_isPercolationGoodSite_nullField (Cbox : ℕ) (u : Lattice d) :
    ¬ IsPercolationGoodSite (nullField d) Cbox false u := by
  intro hgood
  exact hgood 0 u (by simp [InInfluenceBox]) rfl

/-! ## Everything is reachable inside the all-bad set -/

/-- With a step count of at least one, any two sites are joined inside a set
containing every site. -/
theorem jStepReachableIn_of_forall_mem {J : ℕ} (hJ : 1 ≤ J) {S : Set (Lattice d)}
    (hS : ∀ u, u ∈ S) (v w : Lattice d) : JStepReachableIn J S v w := by
  have aux : ∀ t : ℕ, JStepReachableIn J S v (latticeSeg v w t) := by
    intro t
    induction t with
    | zero =>
      rw [latticeSeg_zero]
      refine ⟨[v], rfl, rfl, ?_, ?_⟩
      · intro k hk
        simp at hk
      · intro u _
        exact hS u
    | succ t ih =>
      refine ih.trans ⟨[latticeSeg v w t, latticeSeg v w (t + 1)], rfl, rfl, ?_, ?_⟩
      · rw [isJStepListPath_iff_isChain]
        simpa using (latticeDist_latticeSeg_succ v w t).trans hJ
      · intro u _
        exact hS u
  have := aux (latticeDist v w)
  rwa [latticeSeg_of_dist_le v w (le_refl _)] at this

/-! ## The degenerate reading at step count `0`

For completeness: with `J = 0` the two clauses that the counterexample kills are
*vacuous*, which is why the v1 statement is not refuted at step count zero.  A `0`-step path is constant
(`eq_head_of_isJStepListPath_zero`), so it cannot both meet `B_{l/3}(z)` and
leave `B_{2l/3}(z)`; and the `0`-step component of a site is that site, of
diameter `0`. -/

theorem eq_of_latticeDist_le_zero {x y : Lattice d}
    (h : latticeDist x y ≤ 0) : x = y := by
  funext i
  have hi := (latticeDist_le_iff.mp h) i
  omega

/-- A `0`-step path is constant. -/
theorem eq_head_of_isJStepListPath_zero {path : List (Lattice d)}
    (h : IsJStepListPath 0 path) :
    ∀ k : ℕ, k < path.length → path[k]! = path[0]! := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have h1 : k < path.length := by omega
    have hstep := h k (by omega)
    have heq := eq_of_latticeDist_le_zero hstep
    rw [← heq]
    exact ih h1

theorem exists_index_of_mem {α : Type*} [Inhabited α] {l : List α} {v : α} (h : v ∈ l) :
    ∃ k : ℕ, k < l.length ∧ l[k]! = v := by
  obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp h
  exact ⟨k, hk, by rw [getElem!_pos l k hk]; exact hkv⟩

theorem getElem_bang_zero_of_head? {α : Type*} [Inhabited α] {l : List α} {v : α}
    (h : l.head? = some v) : 0 < l.length ∧ l[0]! = v := by
  cases l with
  | nil => simp at h
  | cons a t =>
    simp at h
    subst h
    exact ⟨by simp, by simp⟩

theorem exists_last_index_of_getLast? {α : Type*} [Inhabited α] {l : List α} {w : α}
    (h : l.getLast? = some w) : ∃ k : ℕ, k + 1 = l.length ∧ l[k]! = w := by
  have hne : l ≠ [] := by
    intro hnil
    rw [hnil] at h
    simp at h
  have hlast : l.getLast hne = w := by
    rw [List.getLast?_eq_some_getLast hne] at h
    exact Option.some_injective _ h
  refine ⟨l.length - 1, by have := List.length_pos_of_ne_nil hne; omega, ?_⟩
  have hidx : l.length - 1 < l.length := by
    have := List.length_pos_of_ne_nil hne; omega
  rw [getElem!_pos l (l.length - 1) hidx, ← hlast, List.getLast_eq_getElem]

/-- A `0`-step component is a single site. -/
theorem eq_of_jStepReachableIn_zero {S : Set (Lattice d)} {v w : Lattice d}
    (h : JStepReachableIn 0 S v w) : v = w := by
  obtain ⟨path, hhead, hlast, hstep, -⟩ := h
  obtain ⟨hpos, hv⟩ := getElem_bang_zero_of_head? hhead
  obtain ⟨k, hk, hw⟩ := exists_last_index_of_getLast? hlast
  have hlk := eq_head_of_isJStepListPath_zero hstep k (by omega)
  rw [hw, hv] at hlk
  exact hlk.symm

theorem jStepComponent_zero_subset (S : Set (Lattice d)) (v : Lattice d) :
    jStepComponent 0 S v ⊆ ({v} : Set (Lattice d)) := by
  intro w hw
  simp only [jStepComponent, mem_ofPred_eq] at hw
  simp only [Set.mem_singleton_iff]
  exact (eq_of_jStepReachableIn_zero hw).symm

/-- **Clause (i) is vacuous at step count `0`.**  A constant path cannot both meet
the inner ball and leave the outer one. -/
theorem crossingClause_vacuous_of_zero_step {z : Lattice d} {l : ℕ}
    {path : List (Lattice d)} (hstep : IsJStepListPath 0 path)
    (h1 : ∃ v ∈ path, InLatticeBallReal z v ((l : ℝ) / 3))
    (h2 : ∃ v ∈ path, ¬ InLatticeBallReal z v (2 * (l : ℝ) / 3)) : False := by
  obtain ⟨v1, hv1, hb1⟩ := h1
  obtain ⟨v2, hv2, hb2⟩ := h2
  obtain ⟨k1, hk1, he1⟩ := exists_index_of_mem hv1
  obtain ⟨k2, hk2, he2⟩ := exists_index_of_mem hv2
  have e1 := eq_head_of_isJStepListPath_zero hstep k1 hk1
  have e2 := eq_head_of_isJStepListPath_zero hstep k2 hk2
  have hveq : v1 = v2 := by rw [← he1, ← he2, e1, e2]
  refine hb2 ?_
  rw [← hveq]
  refine inLatticeBallReal_mono ?_ hb1
  have : (0:ℝ) ≤ (l:ℝ) := Nat.cast_nonneg l
  linarith

theorem hasLatticeDiameterAtMost_singleton (v : Lattice d) {R : ℝ} (hR : 0 ≤ R) :
    HasLatticeDiameterAtMost ({v} : Set (Lattice d)) R := by
  rintro a rfl b rfl i
  simpa using hR

theorem HasLatticeDiameterAtMost.mono {S : Set (Lattice d)} {R R' : ℝ}
    (hRR : R ≤ R') (h : HasLatticeDiameterAtMost S R) :
    HasLatticeDiameterAtMost S R' := by
  intro v hv w hw i
  exact le_trans (h v hv w hw i) hRR

theorem HasLatticeDiameterAtMost.subset {S T : Set (Lattice d)} {R : ℝ}
    (hST : S ⊆ T) (h : HasLatticeDiameterAtMost T R) :
    HasLatticeDiameterAtMost S R := by
  intro v hv w hw i
  exact h v (hST hv) w (hST hw) i

/-- **Clause (ii) is trivial at step count `0`.** -/
theorem badComponentClause_trivial_of_zero_step (S : Set (Lattice d)) (v : Lattice d)
    {R : ℝ} (hR : 0 ≤ R) : HasLatticeDiameterAtMost (jStepComponent 0 S v) R :=
  HasLatticeDiameterAtMost.subset (jStepComponent_zero_subset S v)
    (hasLatticeDiameterAtMost_singleton v hR)

/-! ## The refutation -/

/-- **Clause (ii) fails at the null sample.**  For `1 ≤ J` and `d ≥ 1`, no pair
of counting functions makes `FiniteRangePercolationGeometry` true for the
degenerate field. -/
theorem not_finiteRangePercolationGeometry_nullField {Cbox J : ℕ} (hd : 0 < d)
    (hJ : 1 ≤ J) {c C q : ℝ} (crossing component : Lattice d → Bool → ℕ) :
    ¬ FiniteRangePercolationGeometry (nullField d) Cbox J c C q crossing component := by
  rintro ⟨-, hgeom⟩
  set z : Lattice d := fun _ => (0 : ℤ) with hz
  obtain ⟨-, hbad, -⟩ := hgeom false z
  set B : ℝ := C * (1 + component z false + q⁻¹ * Real.log (2 + 0)) ^ 2 with hB
  have hdiam := hbad 0 le_rfl z (fun i => by simp [hz]) (not_isPercolationGoodSite_nullField _ _)
  set N : ℕ := ⌈B⌉₊ + 1 with hN
  set w : Lattice d := fun _ => (N : ℤ) with hw
  have hall : ∀ u : Lattice d,
      u ∈ {u : Lattice d | ¬ IsPercolationGoodSite (nullField d) Cbox false u} :=
    fun u => not_isPercolationGoodSite_nullField _ _
  have hzmem : z ∈ jStepComponent J
      {u : Lattice d | ¬ IsPercolationGoodSite (nullField d) Cbox false u} z :=
    jStepReachableIn_of_forall_mem hJ hall z z
  have hwmem : w ∈ jStepComponent J
      {u : Lattice d | ¬ IsPercolationGoodSite (nullField d) Cbox false u} z :=
    jStepReachableIn_of_forall_mem hJ hall z w
  have hcoord := hdiam z hzmem w hwmem ⟨0, hd⟩
  have hval : |(z ⟨0, hd⟩ - w ⟨0, hd⟩ : ℤ)| = (N : ℤ) := by
    simp [hz, hw]
  rw [hval] at hcoord
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have hcast : ((N : ℤ) : ℝ) = (⌈B⌉₊ : ℝ) + 1 := by
    rw [hN]; push_cast; ring
  rw [hcast] at hcoord
  linarith

/-- **The statement is false once the step count is at least one.**

The body is the conclusion of `SubdiffusiveProcess.Section9.weighted_multiscale_percolation`,
verbatim. -/
theorem not_weightedMultiscalePercolation_of_one_le_section9CrossingSteps
    {d Cdep : ℕ} (hd : 0 < d) (Cprob cprob : ℝ)
    (hstep : 1 ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d) :
    ¬ (∃ q0 L0 Cbox : ℕ, ∃ c C : ℝ,
      0 < c ∧ 0 < C ∧ 1 ≤ L0 ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (crossing z omega : ℝ) - L0)) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          FiniteRangePercolationGeometry E Cbox
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
            c C q crossing component) := by
  rintro ⟨q0, L0, Cbox, c, C, hc, -, -, hmain⟩
  obtain ⟨crossing, component, -, -, -, -, hgeom⟩ :=
    hmain (Measure.dirac true) (nullField d) (q0 : ℝ) le_rfl
      (fun j z => by rw [measure_nullField]; exact zero_le)
      independentEventScales_nullField
      (multiscaleFiniteRangeIndependentEvents_nullField _)
      translationInvariantEventLaw_nullField
  exact not_finiteRangePercolationGeometry_nullField hd hstep crossing component hgeom

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
