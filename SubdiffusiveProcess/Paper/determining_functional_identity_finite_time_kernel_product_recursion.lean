module

public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.FiniteTime.Kernel
public import MarkovProcess.Kernel.Integral

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace Paper

lemma aux_determining_functional_identity_finite_time_kernel_product_recursion_integrable
    {d m : Nat}
    (g : Fin m → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (μ : Measure (Fin m → SpatialCoordinates d)) [IsFiniteMeasure μ] :
    Integrable (fun path => ∏ i : Fin m, g i (path i)) μ := by
  apply Integrable.of_bound
    ((continuous_finset_prod (s := Finset.univ) (fun i _ =>
      (g i).continuous.comp (continuous_apply i))).aestronglyMeasurable)
    (∏ i : Fin m, ‖g i‖)
  filter_upwards [] with path
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    exact (g i).norm_coe_le_norm (path i)

lemma aux_determining_functional_identity_finite_time_kernel_product_recursion_sum
    {n : Nat} (u : Fin (n + 1) → NNReal) (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j ≤ i.succ), u j) =
      u 0 + ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ i), u j.succ := by
  have hset :
      Finset.univ.filter (fun j : Fin (n + 1) => j ≤ i.succ) =
        insert 0 (Finset.map (Fin.succEmb n)
          (Finset.univ.filter (fun j : Fin n => j ≤ i))) := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.succ_ne_zero, false_or, Finset.mem_map]
      constructor
      · intro hk
        exact ⟨k, Fin.succ_le_succ_iff.mp hk, rfl⟩
      · rintro ⟨a, ha, h⟩
        exact Fin.succ_le_succ_iff.mpr (Fin.succ_injective n h ▸ ha)
  rw [hset, Finset.sum_insert]
  · rw [Finset.sum_map]
    rfl
  · simp



theorem determining_functional_identity_finite_time_kernel_product_recursion
    {d m : Nat}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (u : Fin m → NNReal)
    (times : MarkovProcess.FiniteOrderedTimes m)
    (htimes : ∀ i,
      times i = ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), u j)
    (g : Fin m → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (x : SpatialCoordinates d) :
    (∫ path, ∏ i : Fin m, g i (path i) ∂
      SubMarkovKernelSemigroup.finiteTimeKernel P times x) =
      ((List.finRange m).foldr
        (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
          kernelIntegral (P (u i)) (fun z => g i z * q z) y)
        (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
  induction m generalizing x with
  | zero =>
      letI : IsProbabilityMeasure
          (SubMarkovKernelSemigroup.finiteTimeKernel P times x) :=
        hP.isProbabilityMeasure_finiteTimeLaw P times x
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_zero]
      simp
  | succ n ih =>
      have h0 : times 0 = u 0 := by
        rw [htimes 0]
        have hset :
            Finset.univ.filter (fun j : Fin (n + 1) => j ≤ 0) = {0} := by
          ext j
          simp
        rw [hset]
        simp
      have htail : ∀ i : Fin n,
          times.relativeTail i =
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ i), u j.succ := by
        intro i
        rw [MarkovProcess.FiniteOrderedTimes.relativeTail_apply, htimes i.succ, h0,
          aux_determining_functional_identity_finite_time_kernel_product_recursion_sum,
          add_tsub_cancel_left]
      letI : IsMarkovKernel (P (times 0)) := hP.isMarkovKernel (times 0)
      letI : IsMarkovKernel
          (SubMarkovKernelSemigroup.finiteTimeKernel P times.relativeTail) :=
        hP.isMarkovKernel_finiteTimeKernel P times.relativeTail
      have hcons : Measurable
          (fun z : SpatialCoordinates d × (Fin n → SpatialCoordinates d) =>
            @Fin.cons n (fun _ : Fin (n + 1) => SpatialCoordinates d) z.1 z.2) :=
        MarkovProcess.measurable_finCons
      have hcoord (i : Fin (n + 1)) : Continuous
          (fun z : SpatialCoordinates d × (Fin n → SpatialCoordinates d) =>
            (@Fin.cons n (fun _ : Fin (n + 1) => SpatialCoordinates d) z.1 z.2) i) := by
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using
            (continuous_fst : Continuous
              (Prod.fst : SpatialCoordinates d × (Fin n → SpatialCoordinates d) →
                SpatialCoordinates d))
        · change Continuous
            (fun z : SpatialCoordinates d × (Fin n → SpatialCoordinates d) => z.2 j)
          exact
            (continuous_apply j : Continuous
              (fun path : Fin n → SpatialCoordinates d => path j)).comp
              (continuous_snd : Continuous
                (Prod.snd : SpatialCoordinates d × (Fin n → SpatialCoordinates d) →
                  (Fin n → SpatialCoordinates d)))
      have hcomp_cont : Continuous
          (fun z : SpatialCoordinates d × (Fin n → SpatialCoordinates d) =>
            ∏ i : Fin (n + 1), g i
              ((@Fin.cons n (fun _ : Fin (n + 1) => SpatialCoordinates d)
                z.1 z.2) i)) := by
        apply continuous_finset_prod (s := Finset.univ)
        intro i hi
        exact (g i).continuous.comp (hcoord i)
      have hcomp : Integrable
          (fun z : SpatialCoordinates d × (Fin n → SpatialCoordinates d) =>
            ∏ i : Fin (n + 1), g i
              ((@Fin.cons n (fun _ : Fin (n + 1) => SpatialCoordinates d)
                z.1 z.2) i))
          ((P (times 0) ⊗ₖ
            Kernel.prodMkLeft (SpatialCoordinates d)
              (SubMarkovKernelSemigroup.finiteTimeKernel P times.relativeTail)) x) := by
        apply Integrable.of_bound hcomp_cont.aestronglyMeasurable
          (∏ i : Fin (n + 1), ‖g i‖)
        filter_upwards [] with z
        rw [norm_prod]
        apply Finset.prod_le_prod₀
        · intro i hi
          exact norm_nonneg _
        · intro i hi
          exact (g i).norm_coe_le_norm _
      calc
        (∫ path, ∏ i : Fin (n + 1), g i (path i) ∂
            SubMarkovKernelSemigroup.finiteTimeKernel P times x) =
            ∫ z, (∏ i : Fin (n + 1), g i
              ((@Fin.cons n (fun _ : Fin (n + 1) => SpatialCoordinates d)
                z.1 z.2) i)) ∂
              ((P (times 0) ⊗ₖ
                Kernel.prodMkLeft (SpatialCoordinates d)
                  (SubMarkovKernelSemigroup.finiteTimeKernel P times.relativeTail)) x) := by
          rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ,
            Kernel.mapOfMeasurable_eq_map, Kernel.map_apply _ hcons]
          exact MeasureTheory.integral_map hcons.aemeasurable
            ((continuous_finset_prod (s := Finset.univ) (fun i _ =>
              (g i).continuous.comp (continuous_apply i))).aestronglyMeasurable)
        _ = ∫ a, ∫ b,
              (∏ i : Fin (n + 1), g i
                ((@Fin.cons n (fun _ : Fin (n + 1) => SpatialCoordinates d)
                  a b) i)) ∂
                (Kernel.prodMkLeft (SpatialCoordinates d)
                  (SubMarkovKernelSemigroup.finiteTimeKernel P times.relativeTail) (x, a)) ∂
                (P (times 0) x) :=
          ProbabilityTheory.integral_compProd hcomp
        _ = _ := by
          simp_rw [Kernel.prodMkLeft_apply, Fin.prod_univ_succ,
            Fin.cons_zero, Fin.cons_succ]
          have hih (a : SpatialCoordinates d) :
              (∫ b, ∏ i : Fin n, g i.succ (b i) ∂
                SubMarkovKernelSemigroup.finiteTimeKernel P times.relativeTail a) =
                List.foldr
                  (fun i q y => kernelIntegral (P (u i.succ))
                    (fun z => g i.succ z * q z) y)
                  (fun _ : SpatialCoordinates d => (1 : ℝ))
                  (List.finRange n) a :=
            ih (fun i => u i.succ) times.relativeTail htail
              (fun i => g i.succ) a
          simp_rw [integral_const_mul, hih]
          rw [List.finRange_succ, List.foldr_cons, List.foldr_map, h0]
          rfl

end Paper
end
