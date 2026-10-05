module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.FiniteMarginal
public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.PathMeasure
public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.FiltrationUniqueness
public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.MaximalAssembly

@[expose] public section

/-!
# Cylinders of the path measure, and the reversal

The plumbing that turns `lintegral_pairingChain_gapList_rev` (the finite-dimensional reversal, a
theorem) into `PathReversalInvariance d`.  No new mathematics: the cylinder measure is unfolded to
an iterated pairing and the reversal is applied.

`pathMeasure_indexedCylinder` is the workhorse:

```text
μ {ω | ∀ i, ω (times i) ∈ S i} = ∫ pairingChain 1_{S 0} (gapList times (1_{S ·})).
```

Reading it right to left: the indicator of a cylinder is the **product** of the one-time
indicators; `lintegral_pathMeasure` splits `μ` into `∫ₓ P_x dx`; the path average at finitely many
times is the finite-time kernel (`continuousProcess_map_finiteEvaluation_ordered`); that kernel's
`Fin.cons` recursion is the iterated pairing (`lintegral_finiteTimeKernel_prod`); and the
`x`-integral strips the outer average (`lintegral_fddChain`).

The reversed cylinder needs **no** `Finset.image`: `{ω | ∀ i, ω (T − times i) ∈ S i}` is the
indexed cylinder of the family `times' j = T − times j.rev`, re-indexed by `Fin.rev`, which is
exactly the family `lintegral_pairingChain_gapList_rev` consumes.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set

open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

variable {d : ℕ}

/-- The `ℝ≥0∞`-valued indicator of a set. -/
def indicatorOne (A : Set (Vec d)) : Vec d → ℝ≥0∞ := A.indicator fun _ => 1

theorem measurable_indicatorOne {A : Set (Vec d)} (hA : MeasurableSet A) :
    Measurable (indicatorOne A) :=
  measurable_const.indicator hA

theorem prod_indicatorOne {n : ℕ} (S : Fin n → Set (Vec d)) (y : Fin n → Vec d) :
    (∏ i, indicatorOne (S i) (y i))
      = Set.indicator {z : Fin n → Vec d | ∀ i, z i ∈ S i} (fun _ => (1 : ℝ≥0∞)) y := by
  by_cases h : ∀ i, y i ∈ S i
  · rw [Set.indicator_of_mem (show y ∈ {z : Fin n → Vec d | ∀ i, z i ∈ S i} from h)]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [indicatorOne, Set.indicator_of_mem (h i)]
  · rw [Set.indicator_of_notMem (show y ∉ {z : Fin n → Vec d | ∀ i, z i ∈ S i} from h)]
    push Not at h
    obtain ⟨i, hi⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [indicatorOne, Set.indicator_of_notMem hi]

/-- **The cylinder measure as an iterated pairing.** -/
theorem pathMeasure_indexedCylinder {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (S : Fin (n + 1) → Set (Vec d)) (hS : ∀ i, MeasurableSet (S i)) :
    pathMeasure d {ω : ContinuousPath (Vec d) | ∀ i, ω (times i) ∈ S i}
      = ∫⁻ z, pairingChain (indicatorOne (S 0))
          (gapList times fun i => indicatorOne (S i)) z ∂volume := by
  classical
  set f : Fin (n + 1) → Vec d → ℝ≥0∞ := fun i => indicatorOne (S i) with hfdef
  have hf : ∀ i, Measurable (f i) := fun i => measurable_indicatorOne (hS i)
  have heval : Measurable (ContinuousPath.finiteEvaluation (α := Vec d) fun i => times i) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcylmeas : MeasurableSet {z : Fin (n + 1) → Vec d | ∀ i, z i ∈ S i} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i => (hS i).preimage (measurable_pi_apply i)
  have hAmeas : MeasurableSet {ω : ContinuousPath (Vec d) | ∀ i, ω (times i) ∈ S i} :=
    heval hcylmeas
  have hprodmeas : Measurable fun z : Fin (n + 1) → Vec d => ∏ i, f i (z i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  -- the indicator of the cylinder is the product of the one-time indicators
  have hind : ∀ ω : ContinuousPath (Vec d),
      Set.indicator {ω : ContinuousPath (Vec d) | ∀ i, ω (times i) ∈ S i}
        (1 : ContinuousPath (Vec d) → ℝ≥0∞) ω = ∏ i, f i (ω (times i)) := by
    intro ω
    rw [hfdef, prod_indicatorOne S (fun i => ω (times i))]
    by_cases h : ∀ i, ω (times i) ∈ S i
    · rw [Set.indicator_of_mem
        (show ω ∈ {ω : ContinuousPath (Vec d) | ∀ i, ω (times i) ∈ S i} from h),
        Set.indicator_of_mem
        (show (fun i => ω (times i)) ∈ {z : Fin (n + 1) → Vec d | ∀ i, z i ∈ S i} from h)]
      rfl
    · rw [Set.indicator_of_notMem
        (show ω ∉ {ω : ContinuousPath (Vec d) | ∀ i, ω (times i) ∈ S i} from h),
        Set.indicator_of_notMem
        (show (fun i => ω (times i)) ∉ {z : Fin (n + 1) → Vec d | ∀ i, z i ∈ S i} from h)]
  -- split `μ` and read the inner average as the finite-time kernel
  have hinner : ∀ x : Vec d,
      (∫⁻ ω, ∏ i, f i (ω (times i)) ∂(laplacianContinuousLaw d x)) = fddChain times f x := by
    intro x
    have hmap : (laplacianContinuousLaw d x).map
        (ContinuousPath.finiteEvaluation (α := Vec d) fun i => times i)
        = (laplacianSemigroup d).finiteTimeKernel times x := by
      have h := isFeller_laplacianSemigroup.continuousProcess_map_finiteEvaluation_ordered
        (laplacianSemigroup d) isConservative_laplacianSemigroup
        kolmogorovRegular_laplacianSemigroup times
      have h' := DFunLike.congr_fun h x
      rwa [Kernel.map_apply _ heval] at h'
    rw [← lintegral_finiteTimeKernel_prod times f hf x, ← hmap, lintegral_map hprodmeas heval]
    rfl
  rw [← lintegral_indicator_one hAmeas, lintegral_pathMeasure
    (measurable_one.indicator hAmeas)]
  simp only [hind, hinner]
  exact lintegral_fddChain times f hf

/-! ## Enumerating a finite set of times -/

def finsetTimesOf {n : ℕ} (t : Finset ℝ≥0) (hn : t.card = n + 1) : FiniteOrderedTimes (n + 1) :=
  OrderEmbedding.ofStrictMono (fun i => ((t.orderIsoOfFin hn i : t) : ℝ≥0))
    (fun _ _ hab => (t.orderIsoOfFin hn).strictMono hab)

@[simp] theorem finsetTimesOf_apply {n : ℕ} (t : Finset ℝ≥0) (hn : t.card = n + 1)
    (i : Fin (n + 1)) : finsetTimesOf t hn i = ((t.orderIsoOfFin hn i : t) : ℝ≥0) := rfl

theorem mem_finsetTimesOf {n : ℕ} (t : Finset ℝ≥0) (hn : t.card = n + 1) (q : ℝ≥0) :
    q ∈ t ↔ ∃ i, finsetTimesOf t hn i = q := by
  constructor
  · intro hq
    exact ⟨(t.orderIsoOfFin hn).symm ⟨q, hq⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    exact (t.orderIsoOfFin hn i).2

theorem setOf_forall_mem_eq {n : ℕ} (t : Finset ℝ≥0) (hn : t.card = n + 1)
    (g : ℝ≥0 → ℝ≥0) (S : ℝ≥0 → Set (Vec d)) :
    {ω : ContinuousPath (Vec d) | ∀ q ∈ t, ω (g q) ∈ S q}
      = {ω : ContinuousPath (Vec d) |
          ∀ i, ω (g (finsetTimesOf t hn i)) ∈ S (finsetTimesOf t hn i)} := by
  ext ω
  simp only [mem_ofPred_eq]
  constructor
  · exact fun h i => h _ ((mem_finsetTimesOf t hn _).2 ⟨i, rfl⟩)
  · intro h q hq
    obtain ⟨i, rfl⟩ := (mem_finsetTimesOf t hn q).1 hq
    exact h i

/-! ## Finiteness of the exhausting cylinder -/

theorem nnreal_sub_lt_sub {a b T : ℝ≥0} (hab : a < b) (hbT : b ≤ T) : T - b < T - a := by
  have haT : a ≤ T := hab.le.trans hbT
  refine NNReal.coe_lt_coe.mp ?_
  rw [NNReal.coe_sub hbT, NNReal.coe_sub haT]
  have h : (a : ℝ) < b := hab
  linarith

theorem pathMeasure_eval_zero_cylinder (K : Set (Vec d)) (hK : MeasurableSet K) :
    pathMeasure d {ω : ContinuousPath (Vec d) | ω 0 ∈ K} = volume K := by
  classical
  set times : FiniteOrderedTimes 1 :=
    OrderEmbedding.ofStrictMono (fun _ => (0 : ℝ≥0))
      (fun a b hab => absurd (Subsingleton.elim a b) (ne_of_lt hab)) with htimesdef
  have hset : {ω : ContinuousPath (Vec d) | ω 0 ∈ K}
      = {ω : ContinuousPath (Vec d) | ∀ i : Fin 1, ω (times i) ∈ K} := by
    ext ω
    simp only [mem_ofPred_eq, htimesdef]
    exact ⟨fun h _ => h, fun h => h 0⟩
  rw [hset, pathMeasure_indexedCylinder times (fun _ => K) (fun _ => hK)]
  simp only [gapList, pairingChain_nil, indicatorOne]
  exact lintegral_indicator_one hK

/-! ## The reversal invariance -/

theorem pathReversalInvariance (d : ℕ) : PathReversalInvariance d := by
  classical
  intro T G hG
  have hGamb : Measurable G :=
    hG.mono ((ContinuousPath.canonicalFiltration (alpha := Vec d)).le T) le_rfl
  have hmapG : (∫⁻ ω, G ω ∂((pathMeasure d).map (reversePath T)))
      = ∫⁻ ω, G (reversePath T ω) ∂(pathMeasure d) :=
    lintegral_map hGamb (measurable_reversePath T)
  rw [← hmapG]
  refine (lintegral_eq_of_cylinder_eq (T := T) ?_ ?_ hG).symm
  · intro n
    rw [pathMeasure_eval_zero_cylinder _ Metric.isClosed_closedBall.measurableSet]
    exact (measure_closedBall_lt_top).ne
  · intro t S hle hS
    have hAmeas : MeasurableSet {ω : ContinuousPath (Vec d) | ∀ q ∈ t, ω q ∈ S q} := by
      have hinter : {ω : ContinuousPath (Vec d) | ∀ q ∈ t, ω q ∈ S q}
          = ⋂ q ∈ t, {ω : ContinuousPath (Vec d) | ω q ∈ S q} := by
        ext ω
        simp only [mem_ofPred_eq, Set.mem_iInter]
      rw [hinter]
      exact t.measurableSet_biInter fun q _ =>
        (hS q).preimage (ContinuousPath.measurable_coordinateProcess (alpha := Vec d) q)
    rw [Measure.map_apply (measurable_reversePath T) hAmeas]
    have hpre : reversePath T ⁻¹' {ω : ContinuousPath (Vec d) | ∀ q ∈ t, ω q ∈ S q}
        = {ω : ContinuousPath (Vec d) | ∀ q ∈ t, ω (T - q) ∈ S q} := rfl
    rw [hpre]
    rcases Finset.eq_empty_or_nonempty t with rfl | ht
    · simp
    · obtain ⟨n, hn⟩ : ∃ n, t.card = n + 1 :=
        ⟨t.card - 1, by have := Finset.card_pos.mpr ht; omega⟩
      set times : FiniteOrderedTimes (n + 1) := finsetTimesOf t hn with htdef
      have hmem : ∀ i, times i ∈ t := fun i =>
        (mem_finsetTimesOf t hn _).2 ⟨i, rfl⟩
      have htimes : ∀ i, times i ≤ T := fun i => hle _ (hmem i)
      set times' : FiniteOrderedTimes (n + 1) :=
        OrderEmbedding.ofStrictMono (fun i => T - times i.rev)
          (fun a b hab => nnreal_sub_lt_sub (times.strictMono (Fin.rev_lt_rev.mpr hab))
            (htimes a.rev)) with ht'def
      have hrev : ∀ i : Fin (n + 1), times' i = T - times i.rev := fun _ => rfl
      rw [setOf_forall_mem_eq t hn (fun q => q) S,
        setOf_forall_mem_eq t hn (fun q => T - q) S]
      have hrevset : {ω : ContinuousPath (Vec d) | ∀ i, ω (T - times i) ∈ S (times i)}
          = {ω : ContinuousPath (Vec d) | ∀ j, ω (times' j) ∈ S (times j.rev)} := by
        ext ω
        simp only [mem_ofPred_eq, hrev]
        exact ⟨fun h j => h j.rev, fun h i => by simpa [Fin.rev_rev] using h i.rev⟩
      rw [hrevset,
        pathMeasure_indexedCylinder times (fun i => S (times i)) (fun i => hS _),
        pathMeasure_indexedCylinder times' (fun j => S (times j.rev)) (fun j => hS _)]
      exact lintegral_pairingChain_gapList_rev times times' htimes hrev
        (fun i => indicatorOne (S (times i)))
        (fun i => measurable_indicatorOne (hS _))

/-! ## `maximalEstimateGoal`, unconditionally -/

/-- **`maximalEstimateGoal d`**, with no remaining hypothesis. -/
theorem maximalEstimateGoal_holds (d : ℕ) : maximalEstimateGoal d :=
  maximalEstimateGoal_of_reversalInvariance (pathReversalInvariance d)

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
