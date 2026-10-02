import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeshGluing
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletEnergyContinuity

/-!
# Gluing near-minimizers on disjoint cells, with an affine remainder

Deterministic core of the dilation covariance of `ahom`.  For a nonnegative
continuous weight `a`, a bounded open set `C`, and finitely many pairwise
disjoint measurable cells `V i ⊆ C`,

```text
dirichletInfOn a C p
  ≤ Σ_i dirichletInfOn a (V i) p + ∫_{C \ ⋃ V i} a |p|² .
```

The competitor is `linear_p + Σ_i (zero extension of an ε-minimizer on V i)`;
on the uncovered remainder it is the affine function itself.  No minimizer is
needed (the cells need not be Chapter-2 domains): the proof takes ε-minimizers
from the `sInf` definition and lets ε → 0.  The gluing is the upstream
`exists_h10Function_grad_eq_sum_indicator`.
-/

set_option autoImplicit false

open MeasureTheory Set Homogenization Function
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

namespace AhomDilation

variable {d : ℕ}

/-- **Gluing with an affine remainder.** -/
theorem dirichletInfOn_le_sum_add_remainder {a : Vec d → ℝ} (ha : Continuous a)
    (ha0 : ∀ x, 0 ≤ a x) {C : Set (Vec d)} (hC : IsOpen C)
    (hCb : Bornology.IsBounded C) {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {V : ι → Set (Vec d)} (hVmeas : ∀ i, MeasurableSet (V i))
    (hVC : ∀ i ∈ S, V i ⊆ C) (hdisj : Set.Pairwise (S : Set ι) (Disjoint on V))
    (p : Vec d) :
    dirichletInfOn a C p ≤
      ∑ i ∈ S, dirichletInfOn a (V i) p +
        ∫ x in C \ ⋃ i ∈ S, V i, a x * vecNormSq p := by
  classical
  set W : ι → Set (Vec d) := fun i => C ∩ V i with hWdef
  have hWmeas : ∀ i, MeasurableSet (W i) := fun i => hC.measurableSet.inter (hVmeas i)
  have hWV : ∀ i ∈ S, W i = V i := fun i hi => Set.inter_eq_right.mpr (hVC i hi)
  have hWdisj : Set.Pairwise (S : Set ι) (Disjoint on W) := fun i hi j hj hij =>
    (hdisj hi hj hij).mono Set.inter_subset_right Set.inter_subset_right
  haveI : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hCb.measure_lt_top⟩
  obtain ⟨K, hK⟩ := exists_bound_of_continuous_of_isBounded ha hCb
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set ε' : ℝ := ε / ((S.card : ℝ) + 1) with hε'def
  have hcard1 : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have hε' : 0 < ε' := div_pos hε hcard1
  have hnear : ∀ i, ∃ w : H10Function (W i),
      dirichletEnergyOn' a (W i) p w.toH1Function.grad <
        dirichletInfOn a (W i) p + ε' := by
    intro i
    obtain ⟨E, ⟨w, rfl⟩, hE⟩ := exists_lt_of_csInf_lt
      (dirichletEnergySet_nonempty a (W i) p)
      (lt_add_of_pos_right (dirichletInfOn a (W i) p) hε')
    exact ⟨w, hE⟩
  choose w hw using hnear
  obtain ⟨G, hG⟩ := exists_h10Function_grad_eq_sum_indicator hC S hWmeas
    (fun i => Set.inter_subset_left) w
  set f : Vec d → ℝ := fun x => a x * vecNormSq (p + G.toH1Function.grad x) with hfdef
  have hfint : IntegrableOn f C volume :=
    integrableOn_mul_of_integrableOn_vecNormSq hC.measurableSet ha.measurable hK
      (integrableOn_vecNormSq_add_grad G.toH1Function p)
  have hgrad_in : ∀ i ∈ S, ∀ x ∈ W i,
      G.toH1Function.grad x = (w i).toH1Function.grad x := by
    intro i hi x hx
    rw [hG x]
    refine (Finset.sum_eq_single i ?_ (fun h => absurd hi h)).trans
      (Set.indicator_of_mem hx _)
    intro j hj hji
    exact Set.indicator_of_notMem
      (fun hxj => Set.disjoint_left.mp (hWdisj hj hi hji) hxj hx) _
  have hgrad_out : ∀ x, (∀ i ∈ S, x ∉ W i) → G.toH1Function.grad x = 0 := by
    intro x hx
    rw [hG x]
    exact Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (hx i hi) _
  have hU : (⋃ i ∈ S, W i) ⊆ C := Set.iUnion₂_subset fun i _ => Set.inter_subset_left
  have hUmeas : MeasurableSet (⋃ i ∈ S, W i) :=
    Finset.measurableSet_biUnion S fun i _ => hWmeas i
  have hsplit := integral_inter_add_diff (μ := volume) (f := f) hUmeas hfint
  rw [Set.inter_eq_right.mpr hU] at hsplit
  have hcells : ∫ x in ⋃ i ∈ S, W i, f x = ∑ i ∈ S, ∫ x in W i, f x :=
    integral_biUnion_finset S (fun i _ => hWmeas i) hWdisj
      (fun i _ => hfint.mono_set Set.inter_subset_left)
  have hcell_eq : ∀ i ∈ S, ∫ x in W i, f x =
      dirichletEnergyOn' a (W i) p (w i).toH1Function.grad := by
    intro i hi
    unfold dirichletEnergyOn'
    refine setIntegral_congr_fun (hWmeas i) fun x hx => ?_
    simp only [hfdef, hgrad_in i hi x hx]
  have hset : C \ ⋃ i ∈ S, W i = C \ ⋃ i ∈ S, V i := by
    ext x
    simp only [hWdef, Set.mem_diff, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨hxC, hx⟩
      exact ⟨hxC, fun ⟨i, hi, hxi⟩ => hx ⟨i, hi, hxC, hxi⟩⟩
    · rintro ⟨hxC, hx⟩
      exact ⟨hxC, fun ⟨i, hi, _, hxi⟩ => hx ⟨i, hi, hxi⟩⟩
  have hrem : ∫ x in C \ ⋃ i ∈ S, W i, f x =
      ∫ x in C \ ⋃ i ∈ S, V i, a x * vecNormSq p := by
    rw [hset]
    refine setIntegral_congr_fun
      (hC.measurableSet.diff (Finset.measurableSet_biUnion S fun i _ => hVmeas i))
      fun x hx => ?_
    have hx' : ∀ i ∈ S, x ∉ W i := by
      intro i hi hxi
      exact hx.2 (Set.mem_biUnion hi (Set.inter_subset_right hxi))
    simp only [hfdef, hgrad_out x hx', add_zero]
  have hsumW : ∑ i ∈ S, dirichletInfOn a (W i) p = ∑ i ∈ S, dirichletInfOn a (V i) p :=
    Finset.sum_congr rfl fun i hi => by rw [hWV i hi]
  have hcardε : (S.card : ℝ) * ε' < ε := by
    have h1 : (S.card : ℝ) / ((S.card : ℝ) + 1) < 1 :=
      (div_lt_one hcard1).mpr (by linarith)
    calc (S.card : ℝ) * ε' = ε * ((S.card : ℝ) / ((S.card : ℝ) + 1)) := by
          rw [hε'def]; ring
      _ < ε * 1 := mul_lt_mul_of_pos_left h1 hε
      _ = ε := mul_one ε
  set R : ℝ := ∫ x in C \ ⋃ i ∈ S, V i, a x * vecNormSq p
  calc dirichletInfOn a C p
      ≤ dirichletEnergyOn' a C p G.toH1Function.grad :=
        dirichletInfOn_le hC.measurableSet ha0 G
    _ = ∫ x in C, f x := rfl
    _ = ∑ i ∈ S, dirichletEnergyOn' a (W i) p (w i).toH1Function.grad + R := by
        rw [← hsplit, hcells, hrem, Finset.sum_congr rfl hcell_eq]
    _ ≤ ∑ i ∈ S, (dirichletInfOn a (W i) p + ε') + R := by
        gcongr with i hi
        exact (hw i).le
    _ = ∑ i ∈ S, dirichletInfOn a (V i) p + R + (S.card : ℝ) * ε' := by
        rw [Finset.sum_add_distrib, hsumW, Finset.sum_const, nsmul_eq_mul]
        ring
    _ < ∑ i ∈ S, dirichletInfOn a (V i) p + R + ε := by linarith

end AhomDilation

