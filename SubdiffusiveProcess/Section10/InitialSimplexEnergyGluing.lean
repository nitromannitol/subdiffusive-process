import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeshGluing
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging

/-!
# Finite affine Dirichlet patching with an uncovered remainder

A finite family of disjoint subdomains need not cover the parent. Extend the
attained H₀¹ corrections by zero, sum them, and keep the affine function on
the remainder. This is the finite analytic supplier for the initial simplex
bound in `lim:lem-strict-decay`. It applies to cubes of different scales.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- The part of a parent not occupied by a finite packing. -/
def packingRemainder {ι : Type*} (U : Set (Vec d)) (S : Finset ι)
    (V : ι → Set (Vec d)) : Set (Vec d) :=
  U \ ⋃ i ∈ S, V i

/-- Energy partitions into disjoint packed sets and the uncovered remainder. -/
theorem setIntegral_eq_packing_add_remainder {ι : Type*} [DecidableEq ι]
    {U : Set (Vec d)} (S : Finset ι) (V : ι → Set (Vec d))
    (hU : MeasurableSet U) (hV : ∀ i, MeasurableSet (V i))
    (hsub : ∀ i ∈ S, V i ⊆ U)
    (hdisj : (S : Set ι).PairwiseDisjoint V)
    {f : Vec d → ℝ} (hf : IntegrableOn f U volume) :
    (∫ x in U, f x) = (∑ i ∈ S, ∫ x in V i, f x) +
      ∫ x in packingRemainder U S V, f x := by
  have hcover : (⋃ i ∈ S, V i) ⊆ U := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hsub i hi hxi
  have hmeas : MeasurableSet (⋃ i ∈ S, V i) :=
    S.measurableSet_biUnion (fun i _ => hV i)
  have heq : U = (⋃ i ∈ S, V i) ∪ packingRemainder U S V := by
    rw [packingRemainder, union_diff_cancel hcover]
  calc
    _ = ∫ x in (⋃ i ∈ S, V i) ∪ packingRemainder U S V, f x := by
      exact congrArg (fun A => ∫ x in A, f x) heq
    _ = (∫ x in ⋃ i ∈ S, V i, f x) +
        ∫ x in packingRemainder U S V, f x :=
      setIntegral_union disjoint_sdiff_right (hU.diff hmeas)
        (hf.mono_set hcover) (hf.mono_set diff_subset)
    _ = _ := by
      rw [integral_biUnion_finset S (fun i _ => hV i) hdisj
        (fun i hi => hf.mono_set (hsub i hi))]

/-- On one member of a disjoint packing, only its correction contributes. -/
theorem sum_indicator_eq_on_packing {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (V : ι → Set (Vec d))
    (hdisj : (S : Set ι).PairwiseDisjoint V)
    (G : ι → Vec d → Vec d) {i : ι} (hi : i ∈ S) {x : Vec d} (hx : x ∈ V i) :
    (∑ j ∈ S, (V j).indicator (G j) x) = G i x := by
  classical
  refine (Finset.sum_eq_single i ?_ (fun h => (h hi).elim)).trans
    (indicator_of_mem hx _)
  intro j hj hji
  apply indicator_of_notMem
  intro hxj
  exact disjoint_left.mp (hdisj hj hi hji) hxj hx

/-- Outside the packing, every zero-extended correction vanishes. -/
theorem sum_indicator_eq_zero_on_remainder {ι : Type*}
    (S : Finset ι) (V : ι → Set (Vec d)) (G : ι → Vec d → Vec d)
    {U : Set (Vec d)} {x : Vec d} (hx : x ∈ packingRemainder U S V) :
    (∑ i ∈ S, (V i).indicator (G i) x) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply indicator_of_notMem
  intro hxi
  exact hx.2 (mem_iUnion₂.mpr ⟨i, hi, hxi⟩)

private theorem integrableOn_packing_energy {U : Ch02.Domain d}
    {a : Vec d → ℝ} (ha : Continuous a) (w : H10Function (U : Set (Vec d)))
    (p : Vec d) :
    IntegrableOn (fun x => a x * vecNormSq (p + w.toH1Function.grad x))
      (U : Set (Vec d)) volume := by
  letI := U.isDomain.isFiniteMeasure_restrict_volume
  obtain ⟨C, hC⟩ := exists_bound_of_continuous_of_isBounded ha
    U.isDomain.isBoundedDomain.isBounded
  exact integrableOn_mul_of_integrableOn_vecNormSq U.measurableSet ha.measurable hC
    (integrableOn_vecNormSq_add_grad w.toH1Function p)

/-- Paste actual attained Dirichlet minimizers on a finite disjoint packing,
with the affine competitor on the remainder. The hypothesis concerns only
geometry and a positive continuous coefficient; no energy estimate is assumed. -/
theorem dirichletInfOn_le_packing_add_affine_remainder
    {ι : Type*} [DecidableEq ι] (U : Ch02.Domain d) (S : Finset ι)
    (V : ι → Ch02.Domain d)
    (hsub : ∀ i ∈ S, (V i : Set (Vec d)) ⊆ U)
    (hdisj : (S : Set ι).PairwiseDisjoint (fun i => (V i : Set (Vec d))))
    {a : Vec d → ℝ} (ha : Continuous a) (ha0 : ∀ x, 0 < a x) (p : Vec d) :
    dirichletInfOn a (U : Set (Vec d)) p ≤
      (∑ i ∈ S, dirichletInfOn a (V i : Set (Vec d)) p) +
        ∫ x in packingRemainder (U : Set (Vec d)) S
          (fun i => (V i : Set (Vec d))), a x * vecNormSq p := by
  classical
  have hmin : ∀ i, ∃ w : H10Function (V i : Set (Vec d)),
      dirichletEnergyOn' a (V i : Set (Vec d)) p w.toH1Function.grad =
        dirichletInfOn a (V i : Set (Vec d)) p := fun i =>
    exists_h10Function_dirichletEnergyOn'_eq_dirichletInfOn
      (scalarCoeffOnDataOfContinuousPos ha ha0 (V i)) (fun x => (ha0 x).le) p
  choose w hw using hmin
  -- The library glue asks for subset on every index; indexing by S removes
  -- unused domains without changing the finite packing or its energy.
  let I := {i // i ∈ S}
  let V' : I → Set (Vec d) := fun i => (V i.1 : Set (Vec d))
  let w' : (i : I) → H10Function (V' i) := fun i => w i.1
  obtain ⟨W, hW⟩ := exists_h10Function_grad_eq_sum_indicator U.isOpen
    Finset.univ (fun i : I => (V i.1).measurableSet)
    (fun i : I => hsub i.1 i.2) w'
  have hWsum : ∀ x,
      W.toH1Function.grad x =
        ∑ i ∈ S, (V i : Set (Vec d)).indicator (fun y => (w i).toH1Function.grad y) x := by
    intro x
    rw [hW x]
    exact Finset.sum_coe_sort S (fun i =>
      (V i : Set (Vec d)).indicator (fun y => (w i).toH1Function.grad y) x)
  have hint := integrableOn_packing_energy ha W p
  have hcell : ∀ i ∈ S,
      (∫ x in (V i : Set (Vec d)), a x * vecNormSq (p + W.toH1Function.grad x)) =
        dirichletInfOn a (V i : Set (Vec d)) p := by
    intro i hi
    calc
      _ = dirichletEnergyOn' a (V i : Set (Vec d)) p (w i).toH1Function.grad := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (V i).measurableSet] with x hx
        rw [hWsum x, sum_indicator_eq_on_packing S _ hdisj _ hi hx]
      _ = _ := hw i
  have hrest :
      (∫ x in packingRemainder (U : Set (Vec d)) S (fun i => (V i : Set (Vec d))),
        a x * vecNormSq (p + W.toH1Function.grad x)) =
      ∫ x in packingRemainder (U : Set (Vec d)) S (fun i => (V i : Set (Vec d))),
        a x * vecNormSq p := by
    apply integral_congr_ae
    have hmeas := U.measurableSet.diff
      (S.measurableSet_biUnion (fun i _ => (V i).measurableSet))
    filter_upwards [ae_restrict_mem hmeas] with x hx
    rw [hWsum x, sum_indicator_eq_zero_on_remainder S _ _ hx, add_zero]
  calc
    dirichletInfOn a (U : Set (Vec d)) p ≤
        dirichletEnergyOn' a (U : Set (Vec d)) p W.toH1Function.grad :=
      dirichletInfOn_le U.measurableSet (fun x => (ha0 x).le) W
    _ = (∑ i ∈ S, dirichletInfOn a (V i : Set (Vec d)) p) +
        ∫ x in packingRemainder (U : Set (Vec d)) S (fun i => (V i : Set (Vec d))),
          a x * vecNormSq p := by
      rw [dirichletEnergyOn', setIntegral_eq_packing_add_remainder S _ U.measurableSet
        (fun i => (V i).measurableSet) hsub hdisj hint, hrest]
      congr 1
      exact Finset.sum_congr rfl hcell

end
end SubdiffusiveProcess.Section10
