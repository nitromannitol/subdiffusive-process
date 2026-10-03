module

public import SubdiffusiveProcess.Lane2.LocalRepresentative
public import SubdiffusiveProcess.Lane2.BoundaryPackaging
public import SubdiffusiveProcess.Lane2.KilledTransport

@[expose] public section




open MeasureTheory Set TopologicalSpace Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- **Almost everywhere is everywhere for continuous functions on an open set.**
The set where two continuous functions differ is open in the set, and a
nonempty open subset of `ℝ^d` has positive measure. -/
theorem lane2_eqOn_of_ae_eq_of_continuousOn {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) {f g : SpatialCoordinates d → ℝ}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hae : f =ᵐ[volume.restrict S] g) : ∀ x ∈ S, f x = g x := by
  intro x₀ hx₀
  by_contra hne
  have hcont : ContinuousAt (fun x => f x - g x) x₀ :=
    ((hf.sub hg).continuousAt (hS.mem_nhds hx₀))
  have hzero : (fun x => f x - g x) x₀ ≠ 0 := sub_ne_zero.mpr hne
  have hV : ∀ᶠ x in nhds x₀, (fun x => f x - g x) x ≠ 0 :=
    hcont.eventually_ne hzero
  have hmem : {x : SpatialCoordinates d | (fun y => f y - g y) x ≠ 0} ∩ S
      ∈ nhds x₀ := Filter.inter_mem hV (hS.mem_nhds hx₀)
  obtain ⟨V, hVsub, hVopen, hx₀V⟩ := mem_nhds_iff.mp hmem
  have hae' : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
      x ∈ S → f x = g x := (ae_restrict_iff' hS.measurableSet).mp hae
  have hnullset : volume {x : SpatialCoordinates d | ¬(x ∈ S → f x = g x)} = 0 :=
    ae_iff.mp hae'
  have hnull : volume V = 0 := by
    refine measure_mono_null (fun x hx => ?_) hnullset
    obtain ⟨hx1, hx2⟩ := hVsub hx
    exact fun hcon => hx1 (sub_eq_zero.mpr (hcon hx2))
  have hpos := hVopen.measure_pos volume ⟨x₀, hx₀V⟩
  rw [hnull] at hpos
  exact lt_irrefl _ hpos

/-- The closed box contains the closure of the open box. -/
theorem lane2_closure_openBox_subset (lo hi : SpatialCoordinates d) :
    closure (openBox lo hi : Set (SpatialCoordinates d))
      ⊆ {x : SpatialCoordinates d | ∀ j, lo j ≤ x j ∧ x j ≤ hi j} := by
  refine closure_minimal ?_ ?_
  · intro x hx
    have hx' : x ∈ openBox lo hi := hx
    rw [mem_openBox_iff] at hx'
    exact fun j => ⟨(hx' j).1.le, (hx' j).2.le⟩
  · have : {x : SpatialCoordinates d | ∀ j, lo j ≤ x j ∧ x j ≤ hi j}
        = ⋂ j : Fin d, ({x : SpatialCoordinates d | lo j ≤ x j} ∩
          {x : SpatialCoordinates d | x j ≤ hi j}) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [this]
    exact isClosed_iInter fun j =>
      (isClosed_le continuous_const (continuous_apply j)).inter
        (isClosed_le (continuous_apply j) continuous_const)

/-- **The active set at a boundary point.**  A point of the frontier of a box
lies on at least one face, lies in the closed box, and lies strictly inside the
box in every coordinate whose face it misses. -/
theorem lane2_activeSet_of_mem_frontier {lo hi x₀ : SpatialCoordinates d}
    (hx₀ : x₀ ∈ frontier (openBox lo hi : Set (SpatialCoordinates d))) :
    ∃ (I : Finset (Fin d)) (i₀ : Fin d), i₀ ∈ I ∧
      (∀ i ∈ I, x₀ i = lo i ∨ x₀ i = hi i) ∧
      (∀ j, j ∉ I → lo j < x₀ j ∧ x₀ j < hi j) := by
  classical
  have hclos : x₀ ∈ closure (openBox lo hi : Set (SpatialCoordinates d)) :=
    hx₀.1
  have hIcc := lane2_closure_openBox_subset lo hi hclos
  have hnotin : x₀ ∉ (openBox lo hi : Set (SpatialCoordinates d)) := by
    have hint : interior (openBox lo hi : Set (SpatialCoordinates d))
        = (openBox lo hi : Set (SpatialCoordinates d)) :=
      (openBox lo hi).isOpen.interior_eq
    have := hx₀.2
    rwa [hint] at this
  set I : Finset (Fin d) :=
    Finset.univ.filter (fun j => x₀ j = lo j ∨ x₀ j = hi j) with hI
  have hmemI : ∀ j, j ∈ I ↔ (x₀ j = lo j ∨ x₀ j = hi j) := by
    intro j
    simp [hI]
  have hexists : ∃ i₀ : Fin d, x₀ i₀ = lo i₀ ∨ x₀ i₀ = hi i₀ := by
    by_contra hcon
    push_neg at hcon
    apply hnotin
    show x₀ ∈ openBox lo hi
    rw [mem_openBox_iff]
    intro j
    obtain ⟨h1, h2⟩ := hIcc j
    obtain ⟨h3, h4⟩ := hcon j
    exact ⟨lt_of_le_of_ne h1 (Ne.symm h3), lt_of_le_of_ne h2 h4⟩
  obtain ⟨i₀, hi₀⟩ := hexists
  refine ⟨I, i₀, (hmemI i₀).mpr hi₀, fun i hi => (hmemI i).mp hi, fun j hj => ?_⟩
  have hnj : ¬(x₀ j = lo j ∨ x₀ j = hi j) := fun h => hj ((hmemI j).mpr h)
  push_neg at hnj
  obtain ⟨h1, h2⟩ := hIcc j
  exact ⟨lt_of_le_of_ne h1 (Ne.symm hnj.1), lt_of_le_of_ne h2 hnj.2⟩

/-- **The cell datum is killed.**  A zero trace difference from the smooth datum
makes `u - φ` an element of the killed space, with the expected value and
gradient. -/
theorem lane2_killed_of_zeroTraceDifference {W : Opens (SpatialCoordinates d)}
    {u φ : H1Function (W : Set (SpatialCoordinates d))}
    (htrace : HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φ) :
    ∃ v : SobolevData W, v ∈ killedSobolevGraph W ∧
      ((v.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))]
          fun x => u.toFun x - φ.toFun x) ∧
      (∀ i : Fin d, ((v.2 i : DomainL2 W) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))]
          fun x => u.grad x i - φ.grad x i) := by
  obtain ⟨w, hval, hgrad⟩ := htrace
  obtain ⟨v, hv1, hv2⟩ := Lane4.exists_killedSobolevGraph_of_nativeH10 w
  refine ⟨(v : SobolevData W), v.property, ?_, ?_⟩
  · refine hv1.trans (Filter.EventuallyEq.of_eq ?_)
    funext x
    have := hval x
    linarith [this]
  · intro i
    refine (hv2 i).trans (Filter.EventuallyEq.of_eq ?_)
    funext x
    have := congrFun (hgrad x) i
    simp only [Pi.add_apply] at this
    linarith [this]

/-- A positive bounded coefficient is essentially bounded above. -/
theorem lane2_coeff_ae_bound {W : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient W) :
    ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))),
      ‖((A.val : SpatialCoordinates d → ℝ)) x‖ ≤ C := by
  set mu := volume.restrict (W : Set (SpatialCoordinates d)) with hmu
  have hlt : eLpNormEssSup ((A.val : SpatialCoordinates d → ℝ)) mu < ⊤ := by
    have h := Lp.eLpNorm_lt_top A.val
    rwa [eLpNorm_exponent_top (Lp.aestronglyMeasurable A.val)] at h
  refine ⟨(eLpNormEssSup ((A.val : SpatialCoordinates d → ℝ)) mu).toReal, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup
    (f := ((A.val : SpatialCoordinates d → ℝ))) (μ := mu)] with x hx
  have := ENNReal.toReal_mono hlt.ne hx
  simpa using! this

/-- Products of `L²` gradients against a bounded coefficient are integrable. -/
theorem lane2_integrableOn_coeff_mul {W : Opens (SpatialCoordinates d)}
    {a : SpatialCoordinates d → ℝ} {C : ℝ}
    (hameas : AEStronglyMeasurable a
      (volume.restrict (W : Set (SpatialCoordinates d))))
    (habd : ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))),
      ‖a x‖ ≤ C)
    {f g : SpatialCoordinates d → ℝ}
    (hf : MemLp f 2 (volume.restrict (W : Set (SpatialCoordinates d))))
    (hg : MemLp g 2 (volume.restrict (W : Set (SpatialCoordinates d)))) :
    IntegrableOn (fun x => a x * (f x * g x))
      (W : Set (SpatialCoordinates d)) volume :=
  Integrable.bdd_mul (hf.integrable_mul hg) hameas habd

/-- **The cell datum solves the forced equation.**  If `u` is weakly
`a`-harmonic on the cell and `v = u - φ`, then `v` solves, against every killed
test, the forced equation with the divergence-form load of `a ∇φ`. -/
theorem lane2_cellDatum_solves {W : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient W) {a : SpatialCoordinates d → ℝ}
    (hameas : AEStronglyMeasurable a
      (volume.restrict (W : Set (SpatialCoordinates d))))
    (hA : (A.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))] a)
    {u φ : H1Function (W : Set (SpatialCoordinates d))}
    (hharm : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) u)
    {v : SobolevData W}
    (hv : ∀ i : Fin d, ((v.2 i : DomainL2 W) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))]
        fun x => u.grad x i - φ.grad x i) :
    lane2_SolvesOn A v (fun ψ => -∫ x in (W : Set (SpatialCoordinates d)),
      ∑ i : Fin d, (a x * φ.grad x i) *
        ((ψ.2 i : DomainL2 W) : SpatialCoordinates d → ℝ) x) := by
  classical
  obtain ⟨C, hC⟩ := lane2_coeff_ae_bound A
  have habd : ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))),
      ‖a x‖ ≤ C := by
    filter_upwards [hC, hA] with x h1 h2
    rwa [h2] at h1
  intro ψ hψ
  obtain ⟨χ, hχval, hχgrad⟩ :=
    exists_nativeH10Function_of_killedSobolevGraph (Ω := W) ⟨ψ, hψ⟩
  have hint1 : ∀ i : Fin d, IntegrableOn
      (fun x => a x * (u.grad x i *
        ((ψ.2 i : DomainL2 W) : SpatialCoordinates d → ℝ) x))
      (W : Set (SpatialCoordinates d)) volume := fun i =>
    lane2_integrableOn_coeff_mul hameas habd (u.gradMemL2 i) (Lp.memLp (ψ.2 i))
  have hint2 : ∀ i : Fin d, IntegrableOn
      (fun x => a x * (φ.grad x i *
        ((ψ.2 i : DomainL2 W) : SpatialCoordinates d → ℝ) x))
      (W : Set (SpatialCoordinates d)) volume := fun i =>
    lane2_integrableOn_coeff_mul hameas habd (φ.gradMemL2 i) (Lp.memLp (ψ.2 i))
  have hterm : ∀ i : Fin d,
      (∫ x in (W : Set (SpatialCoordinates d)),
        ((A.val : SpatialCoordinates d → ℝ)) x *
          (((v.2 i : DomainL2 W) : SpatialCoordinates d → ℝ) x *
            ((ψ.2 i : DomainL2 W) : SpatialCoordinates d → ℝ) x))
      = (∫ x in (W : Set (SpatialCoordinates d)),
          a x * (u.grad x i *
            ((ψ.2 i : DomainL2 W) : SpatialCoordinates d → ℝ) x))
        - (∫ x in (W : Set (SpatialCoordinates d)),
          a x * (φ.grad x i *
            ((ψ.2 i : DomainL2 W) : SpatialCoordinates d → ℝ) x)) := by
    intro i
    rw [← integral_sub (hint1 i) (hint2 i)]
    refine integral_congr_ae ?_
    filter_upwards [hA, hv i] with x e1 e2
    rw [e1, e2]
    ring
  rw [Lane4.sobolevCoefficientForm_eq_sum_integral]
  simp only [hterm, Finset.sum_sub_distrib]
  have hzero : (∑ i : Fin d, ∫ x in (W : Set (SpatialCoordinates d)),
      a x * (u.grad x i *
        ((ψ.2 i : DomainL2 W) : SpatialCoordinates d → ℝ) x)) = 0 := by
    have h := hharm χ
    rw [← h]
    rw [← integral_finset_sum _ (fun i _ => hint1 i)]
    refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
    funext x
    rw [vecDot, hχgrad]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hzero, zero_sub]
  congr 1
  rw [← integral_finset_sum _ (fun i _ => hint2 i)]
  refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
  funext x
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **A continuous uniformly elliptic coefficient is a `PositiveCoefficient`.** -/
theorem lane2_exists_positiveCoefficient {U : Opens (SpatialCoordinates d)}
    {a : SpatialCoordinates d → ℝ} (ha : Continuous a) {lam Lam : ℝ}
    (hlam : 0 < lam)
    (hb : ∀ x ∈ (U : Set (SpatialCoordinates d)), lam ≤ a x ∧ a x ≤ Lam) :
    ∃ A : PositiveCoefficient U, ((A.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] a) := by
  have hmemU : ∀ᵐ x ∂(volume.restrict (U : Set (SpatialCoordinates d))),
      x ∈ (U : Set (SpatialCoordinates d)) :=
    ae_restrict_mem U.isOpen.measurableSet
  have hbd : ∀ᵐ x ∂(volume.restrict (U : Set (SpatialCoordinates d))),
      ‖a x‖ ≤ max |lam| |Lam| := by
    filter_upwards [hmemU] with x hx
    obtain ⟨h1, h2⟩ := hb x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have : -|lam| ≤ lam := neg_abs_le lam
      have h3 : -(max |lam| |Lam|) ≤ -|lam| := by
        simpa using! le_max_left |lam| |Lam|
      linarith
    · have : Lam ≤ |Lam| := le_abs_self Lam
      have h4 : |Lam| ≤ max |lam| |Lam| := le_max_right _ _
      linarith
  have hmem : MemLp a (⊤ : ENNReal)
      (volume.restrict (U : Set (SpatialCoordinates d))) :=
    memLp_top_of_bound ha.aestronglyMeasurable _ hbd
  refine ⟨⟨hmem.toLp a, lam, hlam, ?_⟩, MemLp.coeFn_toLp hmem⟩
  filter_upwards [MemLp.coeFn_toLp hmem, hmemU] with x hx hxU
  rw [hx]
  exact (hb x hxU).1

/-- **The `H¹` gradient of a smooth datum is its classical derivative.**  Weak
partial derivatives are unique almost everywhere on an open set, and the
classical derivative of a `C¹` function is one of them. -/
theorem lane2_grad_ae_eq_fderiv {U : Set (SpatialCoordinates d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (φ : H1Function U)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ.toFun) (i : Fin d) :
    (fun x => φ.grad x i)
      =ᵐ[volume.restrict U] fun x => fderiv ℝ φ.toFun x (basisVec i) := by
  have hfin : volume U ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono subset_closure)
      hUb.isCompact_closure.measure_lt_top)
  haveI : IsFiniteMeasure (volume.restrict U) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hfin
  have hgradInt : IntegrableOn (fun x => φ.grad x i) U volume :=
    (φ.gradMemL2 i).integrable (by norm_num)
  have hloc1 : LocallyIntegrableOn (fun x => φ.grad x i) U volume :=
    hgradInt.locallyIntegrableOn
  have hcont : Continuous (fun x => fderiv ℝ φ.toFun x (basisVec i)) := by
    simpa using! ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hloc2 : LocallyIntegrableOn
      (fun x => fderiv ℝ φ.toFun x (basisVec i)) U volume :=
    hcont.locallyIntegrable.locallyIntegrableOn U
  exact HasWeakPartialDerivOn.ae_eq hU hloc1 hloc2
    (φ.hasWeakPartialDerivOn i)
    (HasWeakPartialDerivOn.of_contDiff (hφ.of_le (by simp)))

/-- The cell's forcing `a ∇φ`, truncated to the cell and written with the
classical derivative so that it is globally bounded and measurable. -/
def lane2_cellField (a φ : SpatialCoordinates d → ℝ)
    (U : Set (SpatialCoordinates d)) :
    SpatialCoordinates d → SpatialCoordinates d :=
  fun x i => U.indicator (fun y => a y * fderiv ℝ φ y (basisVec i)) x

theorem lane2_boundedField_cellField {U : Opens (SpatialCoordinates d)}
    (hUb : Bornology.IsBounded (U : Set (SpatialCoordinates d)))
    {a φ : SpatialCoordinates d → ℝ} (ha : Continuous a)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    lane2_BoundedField (lane2_cellField a φ (U : Set (SpatialCoordinates d))) := by
  have hfd : Continuous (fun x => fderiv ℝ φ x) := hφ.continuous_fderiv (by simp)
  have hbdd : Continuous (fun x => |a x| * ‖fderiv ℝ φ x‖) :=
    ha.abs.mul hfd.norm
  obtain ⟨M, hM⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn
    hbdd.continuousOn
  refine ⟨fun i => ?_, ⟨max M 0, fun x i => ?_⟩⟩
  · exact (ha.mul ((hfd.clm_apply continuous_const))).measurable.indicator
      U.isOpen.measurableSet
  · by_cases hx : x ∈ (U : Set (SpatialCoordinates d))
    · rw [lane2_cellField, Set.indicator_of_mem hx]
      have hxc : x ∈ closure (U : Set (SpatialCoordinates d)) := subset_closure hx
      have hbd := hM x hxc
      have hei : ‖(basisVec i : SpatialCoordinates d)‖ ≤ 1 := by
        rw [basisVec]
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun k => ?_)
        by_cases hk : k = i
        · subst hk; simp
        · rw [Pi.single_eq_of_ne hk]; simp
      have h1 : |fderiv ℝ φ x (basisVec i)| ≤ ‖fderiv ℝ φ x‖ := by
        have := (fderiv ℝ φ x).le_opNorm (basisVec i)
        calc |fderiv ℝ φ x (basisVec i)| = ‖fderiv ℝ φ x (basisVec i)‖ := rfl
          _ ≤ ‖fderiv ℝ φ x‖ * ‖(basisVec i : SpatialCoordinates d)‖ := this
          _ ≤ ‖fderiv ℝ φ x‖ * 1 :=
            mul_le_mul_of_nonneg_left hei (norm_nonneg _)
          _ = ‖fderiv ℝ φ x‖ := mul_one _
      have h2 : |a x * fderiv ℝ φ x (basisVec i)| ≤ |a x| * ‖fderiv ℝ φ x‖ := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      have h3 : |a x| * ‖fderiv ℝ φ x‖ ≤ M := by
        simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
          (norm_nonneg _))] using! hbd
      exact le_trans (le_trans h2 h3) (le_max_left _ _)
    · rw [lane2_cellField, Set.indicator_of_notMem hx, abs_zero]
      exact le_max_right _ _

theorem lane2_cellField_isDivLoad {U : Opens (SpatialCoordinates d)}
    (hUb : Bornology.IsBounded (U : Set (SpatialCoordinates d)))
    (a : SpatialCoordinates d → ℝ)
    (φ : H1Function (U : Set (SpatialCoordinates d)))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ.toFun) :
    lane2_IsDivLoad (U := U)
      (fun ψ => -∫ x in (U : Set (SpatialCoordinates d)),
        ∑ i : Fin d, (a x * φ.grad x i) *
          ((ψ.2 i : DomainL2 U) : SpatialCoordinates d → ℝ) x)
      (lane2_cellField a φ.toFun (U : Set (SpatialCoordinates d))) := by
  intro ψ
  simp only
  congr 1
  refine integral_congr_ae ?_
  have hall : ∀ᵐ x ∂(volume.restrict (U : Set (SpatialCoordinates d))),
      ∀ i : Fin d, φ.grad x i = fderiv ℝ φ.toFun x (basisVec i) :=
    ae_all_iff.2 (fun i => lane2_grad_ae_eq_fderiv U.isOpen hUb φ hφ i)
  filter_upwards [hall, ae_restrict_mem U.isOpen.measurableSet] with x hx hxU
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hx i, lane2_cellField, Set.indicator_of_mem hxU]

/-- A bounded measurable field lies in every vector `L^p` class on a bounded
carrier -- in particular in the interior estimate's source class. -/
theorem lane2_memVectorLpOn_of_boundedField
    {U : Set (SpatialCoordinates d)} (hUb : Bornology.IsBounded U)
    {g : SpatialCoordinates d → SpatialCoordinates d}
    (hg : lane2_BoundedField g) (p : ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.MemVectorLpOn U p g := by
  obtain ⟨M0, hM0'⟩ := hg.bdd
  set M : ℝ := max M0 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ (x : SpatialCoordinates d) (i : Fin d), |g x i| ≤ M := fun x i =>
    le_trans (hM0' x i) (le_max_left _ _)
  have hmeas : AEStronglyMeasurable
      (fun x => HilbertVec.ofVec (g x)) (volume.restrict U) := by
    have hm : Measurable (fun x : SpatialCoordinates d => g x) :=
      measurable_pi_lambda (fun i => hg.meas i)
    have hc : Continuous
        (fun v : SpatialCoordinates d => HilbertVec.ofVec v) := by fun_prop
    exact (hc.measurable.comp hm).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict U),
      ‖HilbertVec.ofVec (g x)‖ ≤ Real.sqrt (d : ℝ) * M := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [← euclideanNorm_eq_norm_ofVec, euclideanNorm]
    have hsum : vecNormSq (g x) ≤ (d : ℝ) * M ^ 2 := by
      rw [vecNormSq, vecDot]
      calc ∑ i : Fin d, g x i * g x i ≤ ∑ _i : Fin d, M ^ 2 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have h := hM x i
            nlinarith [abs_nonneg (g x i), sq_abs (g x i)]
        _ = (d : ℝ) * M ^ 2 := by simp
    calc Real.sqrt (vecNormSq (g x)) ≤ Real.sqrt ((d : ℝ) * M ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (d : ℝ) * M := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM0]
  exact lane2_memVectorLpOn_of_bounded hUb hmeas hbound p

/-! ## The local boundary representative -/

/-- **The boundary clause of `HasLocalBoundaryRepresentative`, on a box.**  At a
frontier point the cell is doubled across every active face, the datum `u - φ`
travelling with it as a killed datum solving the forced equation, and the
interior estimate at the now-interior point returns a continuous representative
vanishing there by oddness.  It agrees with `rep - φ` on the overlap because
both are continuous there and agree almost everywhere. -/
theorem lane2_localBoundaryRep_aux [NeZero d] (hd : 2 ≤ d)
    {W : Opens (SpatialCoordinates d)} {lo hi : SpatialCoordinates d}
    (hW : W = openBox lo hi) (hlohi : ∀ j, lo j < hi j)
    {a : SpatialCoordinates d → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (ha : Continuous a)
    (habounds : ∀ x ∈ (W : Set (SpatialCoordinates d)), lam ≤ a x ∧ a x ≤ Lam)
    (φ u : H1Function (W : Set (SpatialCoordinates d)))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ.toFun)
    (hharm : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) u)
    (htrace : HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φ)
    (rep : SpatialCoordinates d → ℝ)
    (hrepcont : ContinuousOn rep (W : Set (SpatialCoordinates d)))
    (hrepae : rep =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))] u.toFun)
    (x₀ : SpatialCoordinates d)
    (hx₀ : x₀ ∈ frontier (W : Set (SpatialCoordinates d))) :
    ∃ S : Set (SpatialCoordinates d), IsOpen S ∧ x₀ ∈ S ∧
      ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g S ∧ g x₀ = 0 ∧
        ∀ y ∈ S ∩ (W : Set (SpatialCoordinates d)),
          g y = rep y - φ.toFun y := by
  classical
  subst hW
  have hWb : Bornology.IsBounded (openBox lo hi : Set (SpatialCoordinates d)) :=
    lane2_isBounded_openBox lo hi
  obtain ⟨I, i₀, hi₀I, hIface, hIo⟩ := lane2_activeSet_of_mem_frontier hx₀
  obtain ⟨v, hvk, hv1, hv2⟩ := lane2_killed_of_zeroTraceDifference htrace
  obtain ⟨A, hA⟩ := lane2_exists_positiveCoefficient ha hlam habounds
  have hsolve : lane2_SolvesOn A v
      (fun ψ => -∫ x in (openBox lo hi : Set (SpatialCoordinates d)),
        ∑ i : Fin d, (a x * φ.grad x i) *
          ((ψ.2 i : DomainL2 (openBox lo hi)) : SpatialCoordinates d → ℝ) x) :=
    lane2_cellDatum_solves A ha.aestronglyMeasurable hA hharm hv2
  have hfield := lane2_boundedField_cellField hWb ha hφ (a := a) (φ := φ.toFun)
  have hdiv := lane2_cellField_isDivLoad hWb a φ hφ
  obtain ⟨lo', hi', P, A', w, L', hw, hsolve2, hfold', hmem, hsub, hmaps, hae,
    hodd, hsym, hoddAll, hdivinv⟩ :=
    lane2_exists_odd_folded_box lo hi x₀ hlohi (I.erase i₀) i₀
      (Finset.notMem_erase i₀ I)
      (fun j hj => hIface j (Finset.mem_of_mem_erase hj))
      (hIface i₀ hi₀I)
      (fun j hj hji => hIo j (fun hjI => hj (Finset.mem_erase.mpr ⟨hji, hjI⟩)))
      a A hA hvk _ hsolve
  obtain ⟨g', hg', hLg'⟩ := hdivinv _ hfield hdiv
  have hax₀ : lam ≤ a x₀ := by
    haveI : (nhdsWithin x₀
        (openBox lo hi : Set (SpatialCoordinates d))).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hx₀.1
    refine ge_of_tendsto
      (ha.continuousWithinAt (s := (openBox lo hi : Set (SpatialCoordinates d)))
        (x := x₀)) ?_
    exact eventually_nhdsWithin_of_forall (fun y hy => (habounds y hy).1)
  have hscont : Continuous
      (foldedCoefficientP a x₀ (insert i₀ (I.erase i₀)) P) :=
    continuous_foldedCoefficientP ha x₀ _ P
  have hspos : 0 < foldedCoefficientP a x₀ (insert i₀ (I.erase i₀)) P x₀ := by
    rw [foldedCoefficientP_fix]
    linarith
  have hB'b : Bornology.IsBounded
      (openBox lo' hi' : Set (SpatialCoordinates d)) :=
    lane2_isBounded_openBox _ _
  have hgLp := lane2_memVectorLpOn_of_boundedField hB'b hg'
    (schauderSourceExponent d (1 / 2))
  have hsolve3 : lane2_SolvesOn A' w
      (fun ψ => -∫ x in (openBox lo' hi' : Set (SpatialCoordinates d)),
        ∑ i : Fin d, g' x i *
          ((ψ.2 i : DomainL2 (openBox lo' hi')) : SpatialCoordinates d → ℝ) x) :=
    fun ψ hψ => (hsolve2 ψ hψ).trans (hLg' ψ)
  have hint : ∀ (p q : H1Function (openBox lo' hi' : Set (SpatialCoordinates d)))
      (i : Fin d), IntegrableOn
      (fun x => ((A'.val : SpatialCoordinates d → ℝ)) x *
        (p.grad x i * q.grad x i))
      (openBox lo' hi' : Set (SpatialCoordinates d)) volume := by
    intro p q i
    obtain ⟨C, hC⟩ := lane2_coeff_ae_bound A'
    exact lane2_integrableOn_coeff_mul (Lp.aestronglyMeasurable A'.val) hC
      (p.gradMemL2 i) (q.gradMemL2 i)
  obtain ⟨rho, vrep, hrho, hballsub, hvcont, hvae, hvzero⟩ :=
    lane2_exists_local_odd_representative hd (openBox lo' hi') x₀ hmem i₀
      (foldedCoefficientP a x₀ (insert i₀ (I.erase i₀)) P) hscont hspos
      A' hfold' w (killedSobolevGraph_le_weakSobolevGraph hw)
      g' (1 / 2) (by constructor <;> norm_num) hgLp hsolve3 hint hodd
  refine ⟨Homogenization.euclideanBall x₀ rho, isOpen_euclideanBall x₀ rho,
    lane2_mem_euclideanBall_self x₀ hrho, vrep, hvcont, hvzero, ?_⟩
  have hopen : IsOpen (Homogenization.euclideanBall x₀ rho ∩
      (openBox lo hi : Set (SpatialCoordinates d))) :=
    (isOpen_euclideanBall x₀ rho).inter (openBox lo hi).isOpen
  refine lane2_eqOn_of_ae_eq_of_continuousOn hopen
    (hvcont.mono Set.inter_subset_left)
    (((hrepcont.mono Set.inter_subset_right).sub
      ((hφ.continuous.continuousOn).mono Set.inter_subset_right))) ?_
  have hsub1 : Homogenization.euclideanBall x₀ rho ∩
      (openBox lo hi : Set (SpatialCoordinates d))
      ⊆ Homogenization.euclideanBall x₀ rho := Set.inter_subset_left
  have hsub2 : Homogenization.euclideanBall x₀ rho ∩
      (openBox lo hi : Set (SpatialCoordinates d))
      ⊆ (openBox lo hi : Set (SpatialCoordinates d)) := Set.inter_subset_right
  have e1 := ae_restrict_of_ae_restrict_of_subset
    (μ := (volume : Measure (SpatialCoordinates d))) hsub1 hvae
  have e2 := ae_restrict_of_ae_restrict_of_subset
    (μ := (volume : Measure (SpatialCoordinates d))) hsub2 hae
  have e3 := ae_restrict_of_ae_restrict_of_subset
    (μ := (volume : Measure (SpatialCoordinates d))) hsub2 hv1
  have e4 := ae_restrict_of_ae_restrict_of_subset
    (μ := (volume : Measure (SpatialCoordinates d))) hsub2 hrepae
  filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]


/-- **The local boundary representative.**  The interior representative is the
canonical ball average; the boundary clause is the reflection argument above. -/
theorem lane2_hasLocalBoundaryRepresentative [NeZero d] (hd : 2 ≤ d) :
    HasLocalBoundaryRepresentative d := by
  classical
  intro c h hh a lam Lam hlam ha habounds φ u hφ hharm htrace
  have hapos : ∀ x ∈ (centeredCube c h hh : Set (SpatialCoordinates d)), 0 < a x :=
    fun x hx => lt_of_lt_of_le hlam (habounds x hx).1
  obtain ⟨hrepcont, hrepae⟩ := lane2_interior_continuous_representative hd
    (centeredCube c h hh).isOpen ha.continuousOn hapos hharm
  refine ⟨euclideanBallAverageRepresentative u.toFun, hrepcont, hrepae, ?_⟩
  intro x₀ hx₀
  have hlohi : ∀ j : Fin d, (fun j => c j - h / 2) j < (fun j => c j + h / 2) j := by
    intro j
    simp only
    linarith
  exact lane2_localBoundaryRep_aux hd (centeredCube_eq_openBox c hh) hlohi hlam
    ha habounds φ u hφ hharm htrace _ hrepcont hrepae x₀ hx₀

/-- **The cell Dirichlet boundary continuity.**  The deferred input of
DEV-008-lane2, now proved. -/
theorem lane2_cellDirichletBoundaryContinuity [NeZero d] (hd : 2 ≤ d) :
    CellDirichletBoundaryContinuity d :=
  cellDirichletBoundaryContinuity_of_localRepresentative
    (lane2_hasLocalBoundaryRepresentative hd)

end SubdiffusiveProcess
