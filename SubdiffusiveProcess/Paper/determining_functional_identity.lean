module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Main.DiffusionPath
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Data.List.FinRange
public import SubdiffusiveProcess.Paper.determining_functional_identity_path_law_product_transport
public import SubdiffusiveProcess.Paper.determining_functional_identity_finite_set_product_integral
public import SubdiffusiveProcess.Paper.determining_functional_identity_finite_time_kernel_product_recursion
public import SubdiffusiveProcess.Paper.determining_functional_identity_positive_increment_laplace_fubini

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

namespace Paper

lemma aux_exp_weight_integrable {k : Nat} (n : Fin k → Nat) (hn : ∀ i, 0 < n i) :
    Integrable (fun s : Fin k → ℝ =>
      Set.indicator (Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)))
        (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) s) volume := by
  let g : Fin k → ℝ → ℝ := fun i t =>
    Set.indicator (Set.Ioi (0 : ℝ)) (fun u => Real.exp (-(n i : ℝ) * u)) t
  have hg : ∀ i, Integrable (g i) volume := by
    intro i
    exact (integrableOn_exp_mul_Ioi (a := -(n i : ℝ))
      (by
        have hi : (0 : ℝ) < (n i : ℝ) := by exact_mod_cast hn i
        exact neg_lt_zero.mpr hi) 0).integrable_indicator measurableSet_Ioi
  have hp : Integrable (fun s : Fin k → ℝ => ∏ i, g i (s i)) volume := by
    simpa only [Measure.pi_univ] using!
      (MeasureTheory.Integrable.fintype_prod (μ := fun _ : Fin k => (volume : Measure ℝ)) hg)
  apply hp.congr
  filter_upwards [] with s
  by_cases hs : s ∈ Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ))
  · rw [Set.mem_pi] at hs
    have hsi : ∀ i, s i ∈ Set.Ioi (0 : ℝ) := fun i => hs i (by simp)
    have hprod : (∏ i, g i (s i)) =
        ∏ i, Real.exp (-(n i : ℝ) * s i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact Set.indicator_of_mem (hsi i) _
    rw [hprod]
    rw [← Real.exp_sum]
    have hsum : (∑ x : Fin k, -(n x : ℝ) * s x) =
        -∑ x : Fin k, (n x : ℝ) * s x := by
      simpa using! (Finset.sum_neg_distrib (s := Finset.univ)
        (fun x : Fin k => (n x : ℝ) * s x))
    rw [hsum]
    exact (Set.indicator_of_mem (Set.mem_pi.mpr hs)
      (fun s : Fin k → ℝ => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i))).symm
  · rw [Set.indicator_of_notMem hs]
    rw [Set.mem_pi] at hs
    push_neg at hs
    obtain ⟨i, _, hi⟩ := hs
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    change Set.indicator (Set.Ioi (0 : ℝ))
      (fun u => Real.exp (-(n i : ℝ) * u)) (s i) = 0
    exact Set.indicator_of_notMem hi _

lemma aux_exp_weight_integral {k : Nat} (n : Fin k → Nat) (hn : ∀ i, 0 < n i) :
    (∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
      Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) =
      ∏ i : Fin k, (n i : ℝ)⁻¹ := by
  let g : Fin k → ℝ → ℝ := fun i t =>
    Set.indicator (Set.Ioi (0 : ℝ)) (fun u => Real.exp (-(n i : ℝ) * u)) t
  have hpoint : (fun s : Fin k → ℝ =>
      Set.indicator (Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)))
        (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) s) =
      (fun s : Fin k → ℝ => ∏ i, g i (s i)) := by
    funext s
    by_cases hs : s ∈ Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ))
    · rw [Set.mem_pi] at hs
      have hsi : ∀ i, s i ∈ Set.Ioi (0 : ℝ) := fun i => hs i (by simp)
      have hprod : (∏ i, g i (s i)) =
          ∏ i, Real.exp (-(n i : ℝ) * s i) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact Set.indicator_of_mem (hsi i) _
      rw [hprod, ← Real.exp_sum]
      have hsum : (∑ x : Fin k, -(n x : ℝ) * s x) =
          -∑ x : Fin k, (n x : ℝ) * s x := by
        simpa using! (Finset.sum_neg_distrib (s := Finset.univ)
          (fun x : Fin k => (n x : ℝ) * s x))
      rw [hsum]
      exact Set.indicator_of_mem (Set.mem_pi.mpr hs)
        (fun s : Fin k → ℝ => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i))
    · rw [Set.indicator_of_notMem hs]
      rw [Set.mem_pi] at hs
      push_neg at hs
      obtain ⟨i, _, hi⟩ := hs
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      change Set.indicator (Set.Ioi (0 : ℝ))
        (fun u => Real.exp (-(n i : ℝ) * u)) (s i) = 0
      exact Set.indicator_of_notMem hi _
  have hmeas : MeasurableSet
      (Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ))) :=
    (measurableSet_pi Set.countable_univ).2
      (Or.inl (fun i hi => measurableSet_Ioi))
  rw [← MeasureTheory.integral_indicator hmeas]
  rw [hpoint, MeasureTheory.integral_fintype_prod_volume_eq_prod]
  congr 1
  funext i
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
    integral_exp_mul_Ioi]
  · simp only [neg_mul, neg_neg, mul_zero, Real.exp_zero, neg_one_mul,
      one_div]
    ring
  · have hi : (0 : ℝ) < (n i : ℝ) := by exact_mod_cast hn i
    exact neg_lt_zero.mpr hi

lemma aux_path_integral_bound {d k : Nat}
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (n : Fin k → Nat) (hn : ∀ i, 0 < n i) (path : DiffusionPath d) :
    |∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
      Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
        ∏ i : Fin k, f i (path (Real.toNNReal
          (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))| ≤
      ∏ i : Fin k, ‖f i‖ / (n i : ℝ) := by
  let S : Set (Fin k → ℝ) := Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ))
  let F : (Fin k → ℝ) → ℝ := fun s =>
    Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
      ∏ i : Fin k, f i (path (Real.toNNReal
        (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))
  have hmeas : MeasurableSet S := by
    dsimp [S]
    exact (measurableSet_pi Set.countable_univ).2
      (Or.inl (fun i hi => measurableSet_Ioi))
  have hweight : Integrable
      (fun s : Fin k → ℝ =>
        Set.indicator S (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) s) volume := by
    exact aux_exp_weight_integrable n hn
  let C : ℝ := ∏ i : Fin k, ‖f i‖
  have hCweight : Integrable
      (fun s : Fin k → ℝ => C * Set.indicator S
        (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) s) volume :=
    hweight.const_mul C
  have hnorm : ∀ s : Fin k → ℝ,
      ‖Set.indicator S F s‖ ≤ C * Set.indicator S
        (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) s := by
    intro s
    by_cases hs : s ∈ S
    · simp only [Set.indicator_of_mem hs]
      calc
        ‖Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
            ∏ i : Fin k, f i (path (Real.toNNReal
              (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))‖ =
            Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
              ∏ i : Fin k, ‖f i (path (Real.toNNReal
                (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_prod]
        _ ≤ Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) * C := by
          apply mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun i hi => norm_nonneg _)
              (fun i hi => (f i).norm_coe_le_norm _))
            (Real.exp_pos _).le
        _ = C * Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) := by ring
    · simp [Set.indicator_of_notMem hs]
  calc
    |∫ s in S, F s| = ‖∫ s, Set.indicator S F s‖ := by
      rw [MeasureTheory.integral_indicator hmeas]
      rfl
    _ ≤ ∫ s, C * Set.indicator S
        (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) s :=
      MeasureTheory.norm_integral_le_of_norm_le hCweight
        (Eventually.of_forall hnorm)
    _ = C * (∫ s in S, Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator hmeas]
    _ = C * ∏ i : Fin k, (n i : ℝ)⁻¹ := by
      rw [aux_exp_weight_integral n hn]
    _ = ∏ i : Fin k, ‖f i‖ / (n i : ℝ) := by
      simp only [div_eq_mul_inv]
      dsimp [C]
      rw [Finset.prod_mul_distrib]

lemma aux_path_integral_continuous {d k : Nat}
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (n : Fin k → Nat) (hn : ∀ i, 0 < n i) :
    Continuous (fun path : DiffusionPath d =>
      ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
        Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
          ∏ i : Fin k, f i (path (Real.toNNReal
            (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))) := by
  let S : Set (Fin k → ℝ) := Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ))
  let C : ℝ := ∏ i : Fin k, ‖f i‖
  let G : DiffusionPath d → (Fin k → ℝ) → ℝ := fun path s =>
    Set.indicator S (fun s =>
      Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
        ∏ i : Fin k, f i (path (Real.toNNReal
          (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))) s
  have hmeas : MeasurableSet S := by
    dsimp [S]
    exact (measurableSet_pi Set.countable_univ).2
      (Or.inl (fun i hi => measurableSet_Ioi))
  have hweight : Integrable
      (fun s : Fin k → ℝ => C * Set.indicator S
        (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) s) volume := by
    exact (aux_exp_weight_integrable n hn).const_mul C
  have hmeasurable : ∀ path : DiffusionPath d, AEStronglyMeasurable (G path) volume := by
    intro path
    apply AEStronglyMeasurable.indicator
    · fun_prop
    · exact hmeas
  have hbound : ∀ path : DiffusionPath d, ∀ᵐ s : Fin k → ℝ, ‖G path s‖ ≤
      C * Set.indicator S
        (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) s := by
    intro path
    filter_upwards [] with s
    dsimp [G, C]
    by_cases hs : s ∈ S
    · simp only [Set.indicator_of_mem hs]
      calc
        ‖Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
            ∏ i : Fin k, f i (path (Real.toNNReal
              (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))‖ =
            Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
              ∏ i : Fin k, ‖f i (path (Real.toNNReal
                (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_prod]
        _ ≤ Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
              ∏ i : Fin k, ‖f i‖ := by
          apply mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun i hi => norm_nonneg _)
              (fun i hi => (f i).norm_coe_le_norm _))
            (Real.exp_pos _).le
        _ = (∏ i : Fin k, ‖f i‖) * Real.exp
              (-∑ i : Fin k, (n i : ℝ) * s i) := by ring
    · simp [Set.indicator_of_notMem hs]
  have hcont : ∀ᵐ s : Fin k → ℝ, Continuous (fun path => G path s) := by
    filter_upwards [] with s
    by_cases hs : s ∈ S
    · simp only [G, Set.indicator_of_mem hs]
      fun_prop
    · simpa [G, Set.indicator_of_notMem hs] using!
        (continuous_const : Continuous (fun _ : DiffusionPath d => (0 : ℝ)))
  have hG : Continuous (fun path : DiffusionPath d => ∫ s, G path s) :=
    MeasureTheory.continuous_of_dominated hmeasurable hbound hweight hcont
  apply hG.congr
  intro path
  rw [MeasureTheory.integral_indicator hmeas]

lemma aux_cumulative_strictMono {k : Nat} (s : Fin k → ℝ) (hs : ∀ i, 0 < s i) :
    StrictMono (fun i : Fin k =>
      Real.toNNReal (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)) := by
  intro i j hij
  let si := Finset.univ.filter (fun q : Fin k => q ≤ i)
  let sj := Finset.univ.filter (fun q : Fin k => q ≤ j)
  have hsub : si ⊆ sj := by
    intro q hq
    have hqi : q ≤ i := (Finset.mem_filter.mp hq).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, hqi.trans hij.le⟩
  have hjmem : j ∈ sj := Finset.mem_filter.mpr ⟨Finset.mem_univ j, le_rfl⟩
  have hjnot : j ∉ si := by
    intro hj
    exact (not_le_of_gt hij) (Finset.mem_filter.mp hj).2
  have hsum : (∑ q ∈ si, s q) < ∑ q ∈ sj, s q := by
    apply Finset.sum_lt_sum_of_subset hsub hjmem hjnot (hs j)
    intro q hq hqnot
    exact (hs q).le
  have hsi : 0 ≤ ∑ q ∈ si, s q :=
    Finset.sum_nonneg (fun q hq => (hs q).le)
  have hsj : 0 ≤ ∑ q ∈ sj, s q :=
    Finset.sum_nonneg (fun q hq => (hs q).le)
  rw [← NNReal.coe_lt_coe]
  simpa [si, sj, Real.coe_toNNReal _ hsi, Real.coe_toNNReal _ hsj] using! hsum

lemma aux_finRange_foldr_cast {m k : Nat} {α : Type}
    (h : m = k) (F : Fin m → α → α) (G : Fin k → α → α) (z : α)
    (hFG : ∀ j, F j = G (Fin.cast h j)) :
    List.foldr F z (List.finRange m) = List.foldr G z (List.finRange k) := by
  subst k
  have hFG' : F = G := by
    funext j
    simpa using! hFG j
  rw [hFG']

lemma aux_finite_time_kernel_product_recursion_integrable
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

lemma aux_finite_time_kernel_product_recursion_sum
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

lemma aux_finite_time_kernel_product_recursion
    {d m : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
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
          aux_finite_time_kernel_product_recursion_sum,
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
        · simpa using!
            (continuous_fst : Continuous
              (Prod.fst : SpatialCoordinates d × (Fin n → SpatialCoordinates d) →
                SpatialCoordinates d))
        · simpa using!
            (continuous_apply j).comp
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

lemma aux_path_integral_fubini {d k : Nat}
    (μ : Measure (DiffusionPath d)) [IsProbabilityMeasure μ]
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (n : Fin k → Nat) (hn : ∀ i, 0 < n i) :
    (∫ path, ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
      Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
        ∏ i : Fin k, f i (path (Real.toNNReal
          (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))) ∂volume ∂μ) =
      ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
        Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
          (∫ path, (∏ i : Fin k, f i (path (Real.toNNReal
            (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))) ∂μ) := by
  let S : Set (Fin k → ℝ) := Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ))
  let T : Set ((Fin k → ℝ) × DiffusionPath d) := S ×ˢ Set.univ
  let C : ℝ := ∏ i : Fin k, ‖f i‖
  let F : (Fin k → ℝ) × DiffusionPath d → ℝ := fun z =>
    T.indicator (fun z =>
      Real.exp (-∑ i : Fin k, (n i : ℝ) * z.1 i) *
        ∏ i : Fin k, f i (z.2 (Real.toNNReal
          (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), z.1 j)))) z
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (measurableSet_pi Set.countable_univ).2
      (Or.inl (fun i hi => measurableSet_Ioi))
  have hT : MeasurableSet T := hS.prod MeasurableSet.univ
  have hFmeas : AEStronglyMeasurable F (volume.prod μ) := by
    apply AEStronglyMeasurable.indicator
    · fun_prop
    · exact hT
  have hD : Integrable (fun z : (Fin k → ℝ) × DiffusionPath d =>
      C * Set.indicator S
        (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) z.1) (volume.prod μ) := by
    exact ((aux_exp_weight_integrable n hn).const_mul C).comp_fst μ
  have hbound : ∀ᵐ z : (Fin k → ℝ) × DiffusionPath d ∂(volume.prod μ),
      ‖F z‖ ≤ C * Set.indicator S
        (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) z.1 := by
    filter_upwards [] with z
    by_cases hz : z.1 ∈ S
    · have hz' : z ∈ T := by exact ⟨hz, Set.mem_univ _⟩
      simp only [F, Set.indicator_of_mem hz', Set.indicator_of_mem hz]
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_prod]
      change Real.exp (-∑ i : Fin k, (n i : ℝ) * z.1 i) *
        ∏ i : Fin k, ‖f i (z.2 (Real.toNNReal
          (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), z.1 j)))‖ ≤
        (∏ i : Fin k, ‖f i‖) * Real.exp (-∑ i : Fin k, (n i : ℝ) * z.1 i)
      dsimp [C]
      calc
        Real.exp (-∑ i : Fin k, (n i : ℝ) * z.1 i) *
            ∏ i : Fin k, ‖f i (z.2 (Real.toNNReal
              (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), z.1 j)))‖ ≤
          Real.exp (-∑ i : Fin k, (n i : ℝ) * z.1 i) * ∏ i : Fin k, ‖f i‖ := by
            apply mul_le_mul_of_nonneg_left
              (Finset.prod_le_prod₀ (fun i hi => norm_nonneg _)
                (fun i hi => (f i).norm_coe_le_norm _))
              (Real.exp_pos _).le
        _ = (∏ i : Fin k, ‖f i‖) *
            Real.exp (-∑ i : Fin k, (n i : ℝ) * z.1 i) := by ring
    · have hz' : z ∉ T := by
        intro hzt
        exact hz hzt.1
      simp [F, Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]
  have hDnonneg : ∀ z : (Fin k → ℝ) × DiffusionPath d, 0 ≤
      C * Set.indicator S
        (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) z.1 := by
    intro z
    dsimp [C]
    by_cases hz : z.1 ∈ S
    · rw [Set.indicator_of_mem hz]
      positivity
    · rw [Set.indicator_of_notMem hz]
      simp
  have hFint : Integrable F (volume.prod μ) := by
    apply hD.mono hFmeas
    filter_upwards [hbound] with z hz
    calc
      ‖F z‖ ≤ C * Set.indicator S
          (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) z.1 := hz
      _ = ‖C * Set.indicator S
          (fun s => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i)) z.1‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hDnonneg z)]
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun s path => F (s, path)) hFint
  calc
    _ = ∫ path, ∫ s, F (s, path) ∂volume ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with path
      rw [← MeasureTheory.integral_indicator hS]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with s
      by_cases hs : s ∈ S
      · simp [F, T, hs]
      · simp [F, T, hs]
    _ = ∫ s, ∫ path, F (s, path) ∂μ ∂volume := hswap.symm
    _ = _ := by
      rw [← MeasureTheory.integral_indicator hS]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with s
      by_cases hs : s ∈ S
      ·
        have hFeq : (fun path : DiffusionPath d => F (s, path)) =
            (fun path => Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
              ∏ i : Fin k, f i (path (Real.toNNReal
                (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))) := by
          funext path
          simp [F, T, hs]
        rw [hFeq]
        rw [MeasureTheory.integral_const_mul]
        simp only [Set.indicator_of_mem hs]
      · simp [F, T, hs, Set.indicator_of_notMem hs]

lemma aux_integral_fin_succ {m : Nat}
    (F : (Fin (m + 1) → ℝ) → ℝ)
    (hF : Integrable (Set.indicator
      (Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Ioi (0 : ℝ))) F) volume) :
    (∫ s in Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Ioi (0 : ℝ)), F s) =
      ∫ t in Set.Ioi (0 : ℝ),
        ∫ r in Set.pi Set.univ (fun _ : Fin m => Set.Ioi (0 : ℝ)),
          F (Fin.cons t r) := by
  let S : Set (Fin (m + 1) → ℝ) :=
    Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Ioi (0 : ℝ))
  let T : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ : Fin m => Set.Ioi (0 : ℝ))
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (measurableSet_pi Set.countable_univ).2
      (Or.inl (fun i hi => measurableSet_Ioi))
  have hT : MeasurableSet T := by
    dsimp [T]
    exact (measurableSet_pi Set.countable_univ).2
      (Or.inl (fun i hi => measurableSet_Ioi))
  rw [← MeasureTheory.integral_indicator hS]
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
  let hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => (volume : Measure ℝ)) 0).symm
  have hcomp :
      (∫ z, (Set.indicator S F) (e z) ∂(volume.prod
        (Measure.pi (fun _ : Fin m => (volume : Measure ℝ)))) ) =
        ∫ s, Set.indicator S F s := hp.integral_comp' _
  rw [← hcomp]
  change (∫ z : ℝ × (Fin m → ℝ),
      (Set.indicator S F)
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm z)
        ∂(volume.prod (Measure.pi (fun _ : Fin m => (volume : Measure ℝ))))) = _
  have heq (t : ℝ) (r : Fin m → ℝ) :
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
          (t, r) = Fin.cons t r := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simp_rw [heq]
  rw [MeasureTheory.integral_prod]
  · rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · have hScons : (fun r : Fin m → ℝ =>
          (Set.indicator S F) (Fin.cons t r)) =
          T.indicator (fun r => F (Fin.cons t r)) := by
        funext r
        by_cases hr : r ∈ T
        · have hcons_mem : Fin.cons t r ∈ S := by
            rw [Set.mem_pi]
            intro i hi
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa [Set.mem_Ioi] using! ht
            · exact (Set.mem_pi.mp hr) j (by simp)
          simp only [Set.indicator_of_mem hcons_mem,
            Set.indicator_of_mem hr]
        · have hcons_not : Fin.cons t r ∉ S := by
            intro hcons
            apply hr
            rw [Set.mem_pi]
            intro j hj
            exact (Set.mem_pi.mp hcons) (Fin.succ j) (by simp)
          simp only [Set.indicator_of_notMem hcons_not,
            Set.indicator_of_notMem hr]
      rw [hScons]
      rw [MeasureTheory.integral_indicator hT]
      simp [T, ht]
      rfl
    · have hzero : (fun r : Fin m → ℝ =>
          (Set.indicator S F) (Fin.cons t r)) = 0 := by
        funext r
        have hcons_not : Fin.cons t r ∉ S := by
          intro hcons
          have h0 := (Set.mem_pi.mp hcons) 0 (by simp)
          have h0' : 0 < t := by
            simpa [Set.mem_Ioi] using! h0
          have ht' : ¬ 0 < t := by
            simpa [Set.mem_Ioi] using! ht
          exact ht' h0'
        exact Set.indicator_of_notMem hcons_not _
      rw [hzero]
      simp [ht]
  · have hFp : Integrable (fun z => (Set.indicator S F) (e z))
        (volume.prod (Measure.pi (fun _ : Fin m => (volume : Measure ℝ)))) := by
      exact hp.integrable_comp_of_integrable hF
    simpa [e, S] using! hFp



theorem determining_functional_identity
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (RN : Nat → BilateralField d → Nat → (SpatialCoordinates d → ℝ) →
      SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega n f x, RN N omega n f x =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) *
        kernelIntegral (PN N omega (Real.toNNReal t)) f x)
    (k : Nat)
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (n : Fin k → Nat)
    (hn : ∀ i, 0 < n i)
    (Psi : DiffusionPath d → ℝ)
    (hPsi : ∀ path, Psi path =
      ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
        Real.exp (-(∑ i : Fin k, (n i : ℝ) * s i)) *
          ∏ i : Fin k, f i (path (Real.toNNReal
            (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))) :
    Continuous Psi ∧
    (∀ path, |Psi path| ≤ ∏ i : Fin k, ‖f i‖ / (n i : ℝ)) ∧
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N x,
      ∫ path, Psi path ∂(KN N (omega, x)) =
        ((List.finRange k).foldr
          (fun i (g : SpatialCoordinates d → ℝ) => fun y =>
            RN N omega (n i) (fun z => f i z * g z) y)
          (fun _ : SpatialCoordinates d => (1 : ℝ))) x) ∧
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N x,
      (∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
        Real.exp (-(∑ i : Fin k, (n i : ℝ) * s i)) *
          (∫ path, (∏ i : Fin k, f i (path (Real.toNNReal
            (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
            ∂(KN N (omega, x)))) =
        ((List.finRange k).foldr
          (fun i (g : SpatialCoordinates d → ℝ) => fun y =>
            RN N omega (n i) (fun z => f i z * g z) y)
          (fun _ : SpatialCoordinates d => (1 : ℝ))) x) := by
  rcases hin with ⟨hres, hcons, hmap⟩
  have hmap' := determining_functional_identity_path_law_product_transport
    M H PN KN hKN ⟨hres, hcons, hmap⟩
  have hFourth :
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N x,
        (∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
          Real.exp (-(∑ i : Fin k, (n i : ℝ) * s i)) *
            (∫ path, (∏ i : Fin k, f i (path (Real.toNNReal
              (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
              ∂(KN N (omega, x)))) =
        ((List.finRange k).foldr
          (fun i (g : SpatialCoordinates d → ℝ) => fun y =>
            RN N omega (n i) (fun z => f i z * g z) y)
          (fun _ : SpatialCoordinates d => (1 : ℝ))) x) := by
    filter_upwards [hmap'] with omega hω
    intro N x
    let P : SubMarkovKernelSemigroup (SpatialCoordinates d) := PN N omega
    have hP : P.IsConservative := hcons N omega
    have hinner : ∀ s ∈ Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
        (∫ path, (∏ i : Fin k, f i (path (Real.toNNReal
          (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
            ∂(KN N (omega, x))) =
        ((List.finRange k).foldr
          (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
            kernelIntegral (P (Real.toNNReal (s i)) )
              (fun z => f i z * q z) y)
          (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
      intro s hs
      have hspos : ∀ i : Fin k, 0 < s i := by
        intro i
        exact (Set.mem_pi.mp hs) i (by simp)
      let τ : Fin k → NNReal := fun i =>
        Real.toNNReal (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)
      have hτ : StrictMono τ := by
        exact aux_cumulative_strictMono s hspos
      let I : Finset NNReal := Finset.univ.image τ
      have hI : I.card = k := by
        dsimp [I]
        rw [Finset.card_image_of_injective _ hτ.injective, Finset.card_univ,
          Fintype.card_fin]
      have horder : τ = I.orderEmbOfFin hI := by
        apply Finset.orderEmbOfFin_unique hI
        · intro i
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        · exact hτ
      have hτmem : ∀ i : Fin k, τ i ∈ I := by
        intro i
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      let g : I → BoundedContinuousFunction (SpatialCoordinates d) ℝ := fun t =>
        f ((I.orderIsoOfFin hI).symm t)
      have hgprod : ∀ path : I → SpatialCoordinates d,
          (∏ t : I, g t (path t)) =
            ∏ i : Fin k, f i (path ⟨τ i, hτmem i⟩) := by
        intro path
        apply Fintype.prod_equiv (I.orderIsoOfFin hI).symm
        intro t
        have ht : τ ((I.orderIsoOfFin hI).symm t) = (t : NNReal) := by
          rw [horder]
          change I.orderEmbOfFin hI ((I.orderIsoOfFin hI).symm t) = (t : NNReal)
          rw [← Finset.coe_orderIsoOfFin_apply]
          exact congrArg (fun u : I => (u : NNReal))
            ((I.orderIsoOfFin hI).apply_symm_apply t)
        simp only [g]
        congr 2
        apply Subtype.ext
        exact ht.symm
      have hτtimes : ∀ j : Fin I.card, τ (Fin.cast hI j) =
          SubMarkovKernelSemigroup.finiteSetTimes I j := by
        have heq : (fun j : Fin I.card => τ (Fin.cast hI j)) =
            I.orderEmbOfFin rfl := by
          apply Finset.orderEmbOfFin_unique rfl
          · intro j
            exact hτmem (Fin.cast hI j)
          · exact hτ.comp (Fin.castOrderIso hI).toOrderEmbedding.strictMono
        intro j
        simpa only [SubMarkovKernelSemigroup.finiteSetTimes] using! congrFun heq j
      let u : Fin I.card → NNReal := fun j =>
        Real.toNNReal (s (Fin.cast hI j))
      have htimes : ∀ j : Fin I.card,
          SubMarkovKernelSemigroup.finiteSetTimes I j =
            ∑ q ∈ Finset.univ.filter (fun q : Fin I.card => q ≤ j), u q := by
        intro j
        have hsum :
            (∑ q ∈ Finset.univ.filter (fun q : Fin I.card => q ≤ j),
              s (Fin.cast hI q)) =
            ∑ r ∈ Finset.univ.filter
              (fun r : Fin k => r ≤ Fin.cast hI j), s r := by
          apply Finset.sum_equiv (Fin.castOrderIso hI)
          · intro q
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact (Fin.castOrderIso hI).le_iff_le
          · intro q hq
            rfl
        rw [← hτtimes j]
        apply NNReal.eq
        have hleft : 0 ≤ ∑ r ∈ Finset.univ.filter
              (fun r : Fin k => r ≤ Fin.cast hI j), s r :=
          Finset.sum_nonneg (fun r hr => (hspos r).le)
        rw [Real.coe_toNNReal _ hleft]
        simp only [u, NNReal.coe_sum]
        rw [← hsum]
        simp_rw [Real.coe_toNNReal _ (hspos _).le]
      have htransport :
          (∫ path, (∏ i : Fin k, f i (path (Real.toNNReal
            (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
              ∂(KN N (omega, x))) =
            ∫ y, ∏ t : I, g t (y t) ∂(P.finiteSetKernel I x) := by
        calc
          _ = ∫ path, ∏ t : I, g t (path (t : NNReal)) ∂(KN N (omega, x)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with path
            simpa [τ] using!
              (hgprod (fun t : I => path (t : NNReal))).symm
          _ = ∫ y, ∏ t : I, g t (y t) ∂(P.finiteSetKernel I x) := by
            simpa [P] using! hω N I x g
      let gtime : Fin I.card → BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
        fun j => g ⟨SubMarkovKernelSemigroup.finiteSetTimes I j,
          Finset.orderEmbOfFin_mem I rfl j⟩
      have hrec :=
        aux_finite_time_kernel_product_recursion
          (P := P) hP u (SubMarkovKernelSemigroup.finiteSetTimes I) htimes gtime x
      have hset := determining_functional_identity_finite_set_product_integral
        (P := P) hP I g x
      have hfinite :
          (∫ y, ∏ t : I, g t (y t) ∂(P.finiteSetKernel I x)) =
            ((List.finRange I.card).foldr
              (fun j (q : SpatialCoordinates d → ℝ) => fun y =>
                kernelIntegral (P (u j)) (fun z => gtime j z * q z) y)
              (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
        calc
          _ = ∫ path, ∏ j : Fin I.card, gtime j (path j) ∂
              (P.finiteTimeKernel (SubMarkovKernelSemigroup.finiteSetTimes I) x) := hset
          _ = _ := hrec
      have hgtime : ∀ j : Fin I.card, gtime j = f (Fin.cast hI j) := by
        intro j
        dsimp [gtime, g]
        congr 1
        apply (I.orderIsoOfFin hI).injective
        rw [OrderIso.apply_symm_apply]
        apply Subtype.ext
        change (SubMarkovKernelSemigroup.finiteSetTimes I j : NNReal) =
          ((I.orderIsoOfFin hI) (Fin.cast hI j) : NNReal)
        rw [← hτtimes j, horder]
        rw [← Finset.coe_orderIsoOfFin_apply]
      have hfold :
          ((List.finRange I.card).foldr
            (fun j (q : SpatialCoordinates d → ℝ) => fun y =>
              kernelIntegral (P (u j)) (fun z => gtime j z * q z) y)
            (fun _ : SpatialCoordinates d => (1 : ℝ))) x =
            ((List.finRange k).foldr
              (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
                kernelIntegral (P (Real.toNNReal (s i)))
                  (fun z => f i z * q z) y)
              (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
        apply congrFun
          (aux_finRange_foldr_cast hI
            (fun j (q : SpatialCoordinates d → ℝ) => fun y =>
              kernelIntegral (P (u j)) (fun z => gtime j z * q z) y)
            (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
              kernelIntegral (P (Real.toNNReal (s i)))
                (fun z => f i z * q z) y)
            (fun _ : SpatialCoordinates d => (1 : ℝ)) (by
              intro j
              rw [hgtime j]
              )) x
      exact htransport.trans (hfinite.trans hfold)
    have houter :=
      determining_functional_identity_positive_increment_laplace_fubini
        (P := P) hP
        (fun r q y => RN N omega r q y)
        (fun r q y => hRN N omega r q y)
        f n hn x
    calc
      (∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
          Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
            (∫ path, (∏ i : Fin k, f i (path (Real.toNNReal
              (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
              ∂(KN N (omega, x)))) =
          ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
            Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
              ((List.finRange k).foldr
                (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
                  kernelIntegral (P (Real.toNNReal (s i)) )
                    (fun z => f i z * q z) y)
                (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [ae_restrict_mem (show MeasurableSet
          (Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ))) from
            (measurableSet_pi Set.countable_univ).2
              (Or.inl (fun i hi => measurableSet_Ioi)))] with s hs
        rw [hinner s hs]
      _ = ((List.finRange k).foldr
          (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
            RN N omega (n i) (fun z => f i z * q z) y)
          (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
        simpa [P] using! houter
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (aux_path_integral_continuous f n hn).congr
    intro path
    exact (hPsi path).symm
  · intro path
    rw [hPsi path]
    exact aux_path_integral_bound f n hn path
  · filter_upwards [hFourth] with omega h4
    intro N x
    letI : IsMarkovKernel (KN N) := hKN N
    have hfub := aux_path_integral_fubini (KN N (omega, x)) f n hn
    calc
      (∫ path, Psi path ∂(KN N (omega, x))) =
          ∫ path, ∫ s in Set.pi Set.univ
            (fun _ : Fin k => Set.Ioi (0 : ℝ)),
              Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
                ∏ i : Fin k, f i (path (Real.toNNReal
                  (∑ j ∈ Finset.univ.filter
                    (fun j : Fin k => j ≤ i), s j))) ∂volume ∂(KN N (omega, x)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with path
        exact hPsi path
      _ = ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
          Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
            (∫ path, (∏ i : Fin k, f i (path (Real.toNNReal
              (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
              ∂(KN N (omega, x))) := hfub
      _ = ((List.finRange k).foldr
          (fun i (g : SpatialCoordinates d → ℝ) => fun y =>
            RN N omega (n i) (fun z => f i z * g z) y)
          (fun _ : SpatialCoordinates d => (1 : ℝ))) x := h4 N x
  · filter_upwards [hmap'] with omega hω
    intro N x
    let P : SubMarkovKernelSemigroup (SpatialCoordinates d) := PN N omega
    have hP : P.IsConservative := hcons N omega
    have hinner : ∀ s ∈ Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
        (∫ path, (∏ i : Fin k, f i (path (Real.toNNReal
          (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
            ∂(KN N (omega, x))) =
        ((List.finRange k).foldr
          (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
            kernelIntegral (P (Real.toNNReal (s i)) )
              (fun z => f i z * q z) y)
          (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
      intro s hs
      have hspos : ∀ i : Fin k, 0 < s i := by
        intro i
        exact (Set.mem_pi.mp hs) i (by simp)
      let τ : Fin k → NNReal := fun i =>
        Real.toNNReal (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)
      have hτ : StrictMono τ := by
        exact aux_cumulative_strictMono s hspos
      let I : Finset NNReal := Finset.univ.image τ
      have hI : I.card = k := by
        dsimp [I]
        rw [Finset.card_image_of_injective _ hτ.injective, Finset.card_univ,
          Fintype.card_fin]
      have horder : τ = I.orderEmbOfFin hI := by
        apply Finset.orderEmbOfFin_unique hI
        · intro i
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        · exact hτ
      have hτmem : ∀ i : Fin k, τ i ∈ I := by
        intro i
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      let g : I → BoundedContinuousFunction (SpatialCoordinates d) ℝ := fun t =>
        f ((I.orderIsoOfFin hI).symm t)
      have hgprod : ∀ path : I → SpatialCoordinates d,
          (∏ t : I, g t (path t)) =
            ∏ i : Fin k, f i (path ⟨τ i, hτmem i⟩) := by
        intro path
        apply Fintype.prod_equiv (I.orderIsoOfFin hI).symm
        intro t
        have ht : τ ((I.orderIsoOfFin hI).symm t) = (t : NNReal) := by
          rw [horder]
          change I.orderEmbOfFin hI ((I.orderIsoOfFin hI).symm t) = (t : NNReal)
          rw [← Finset.coe_orderIsoOfFin_apply]
          exact congrArg (fun u : I => (u : NNReal))
            ((I.orderIsoOfFin hI).apply_symm_apply t)
        simp only [g]
        congr 2
        apply Subtype.ext
        exact ht.symm
      have hτtimes : ∀ j : Fin I.card, τ (Fin.cast hI j) =
          SubMarkovKernelSemigroup.finiteSetTimes I j := by
        have heq : (fun j : Fin I.card => τ (Fin.cast hI j)) =
            I.orderEmbOfFin rfl := by
          apply Finset.orderEmbOfFin_unique rfl
          · intro j
            exact hτmem (Fin.cast hI j)
          · exact hτ.comp (Fin.castOrderIso hI).toOrderEmbedding.strictMono
        intro j
        simpa only [SubMarkovKernelSemigroup.finiteSetTimes] using! congrFun heq j
      let u : Fin I.card → NNReal := fun j =>
        Real.toNNReal (s (Fin.cast hI j))
      have htimes : ∀ j : Fin I.card,
          SubMarkovKernelSemigroup.finiteSetTimes I j =
            ∑ q ∈ Finset.univ.filter (fun q : Fin I.card => q ≤ j), u q := by
        intro j
        have hsum :
            (∑ q ∈ Finset.univ.filter (fun q : Fin I.card => q ≤ j),
              s (Fin.cast hI q)) =
            ∑ r ∈ Finset.univ.filter
              (fun r : Fin k => r ≤ Fin.cast hI j), s r := by
          apply Finset.sum_equiv (Fin.castOrderIso hI)
          · intro q
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact (Fin.castOrderIso hI).le_iff_le
          · intro q hq
            rfl
        rw [← hτtimes j]
        apply NNReal.eq
        have hleft : 0 ≤ ∑ r ∈ Finset.univ.filter
              (fun r : Fin k => r ≤ Fin.cast hI j), s r :=
          Finset.sum_nonneg (fun r hr => (hspos r).le)
        rw [Real.coe_toNNReal _ hleft]
        simp only [u, NNReal.coe_sum]
        rw [← hsum]
        simp_rw [Real.coe_toNNReal _ (hspos _).le]
      have htransport :
          (∫ path, (∏ i : Fin k, f i (path (Real.toNNReal
            (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
              ∂(KN N (omega, x))) =
            ∫ y, ∏ t : I, g t (y t) ∂(P.finiteSetKernel I x) := by
        calc
          _ = ∫ path, ∏ t : I, g t (path (t : NNReal)) ∂(KN N (omega, x)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with path
            simpa [τ] using!
              (hgprod (fun t : I => path (t : NNReal))).symm
          _ = ∫ y, ∏ t : I, g t (y t) ∂(P.finiteSetKernel I x) := by
            simpa [P] using! hω N I x g
      let gtime : Fin I.card → BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
        fun j => g ⟨SubMarkovKernelSemigroup.finiteSetTimes I j,
          Finset.orderEmbOfFin_mem I rfl j⟩
      have hrec :=
        aux_finite_time_kernel_product_recursion
          (P := P) hP u (SubMarkovKernelSemigroup.finiteSetTimes I) htimes gtime x
      have hset := determining_functional_identity_finite_set_product_integral
        (P := P) hP I g x
      have hfinite :
          (∫ y, ∏ t : I, g t (y t) ∂(P.finiteSetKernel I x)) =
            ((List.finRange I.card).foldr
              (fun j (q : SpatialCoordinates d → ℝ) => fun y =>
                kernelIntegral (P (u j)) (fun z => gtime j z * q z) y)
              (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
        calc
          _ = ∫ path, ∏ j : Fin I.card, gtime j (path j) ∂
              (P.finiteTimeKernel (SubMarkovKernelSemigroup.finiteSetTimes I) x) := hset
          _ = _ := hrec
      have hgtime : ∀ j : Fin I.card, gtime j = f (Fin.cast hI j) := by
        intro j
        dsimp [gtime, g]
        congr 1
        apply (I.orderIsoOfFin hI).injective
        rw [OrderIso.apply_symm_apply]
        apply Subtype.ext
        change (SubMarkovKernelSemigroup.finiteSetTimes I j : NNReal) =
          ((I.orderIsoOfFin hI) (Fin.cast hI j) : NNReal)
        rw [← hτtimes j, horder]
        rw [← Finset.coe_orderIsoOfFin_apply]
      have hfold :
          ((List.finRange I.card).foldr
            (fun j (q : SpatialCoordinates d → ℝ) => fun y =>
              kernelIntegral (P (u j)) (fun z => gtime j z * q z) y)
            (fun _ : SpatialCoordinates d => (1 : ℝ))) x =
            ((List.finRange k).foldr
              (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
                kernelIntegral (P (Real.toNNReal (s i)))
                  (fun z => f i z * q z) y)
              (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
        apply congrFun
          (aux_finRange_foldr_cast hI
            (fun j (q : SpatialCoordinates d → ℝ) => fun y =>
              kernelIntegral (P (u j)) (fun z => gtime j z * q z) y)
            (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
              kernelIntegral (P (Real.toNNReal (s i)))
                (fun z => f i z * q z) y)
            (fun _ : SpatialCoordinates d => (1 : ℝ)) (by
              intro j
              rw [hgtime j]
              )) x
      exact htransport.trans (hfinite.trans hfold)
    have houter :=
      determining_functional_identity_positive_increment_laplace_fubini
        (P := P) hP
        (fun r q y => RN N omega r q y)
        (fun r q y => hRN N omega r q y)
        f n hn x
    calc
      (∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
          Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
            (∫ path, (∏ i : Fin k, f i (path (Real.toNNReal
              (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
              ∂(KN N (omega, x)))) =
          ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
            Real.exp (-∑ i : Fin k, (n i : ℝ) * s i) *
              ((List.finRange k).foldr
                (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
                  kernelIntegral (P (Real.toNNReal (s i)) )
                    (fun z => f i z * q z) y)
                (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [ae_restrict_mem (show MeasurableSet
          (Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ))) from
            (measurableSet_pi Set.countable_univ).2
              (Or.inl (fun i hi => measurableSet_Ioi)))] with s hs
        rw [hinner s hs]
      _ = ((List.finRange k).foldr
          (fun i (q : SpatialCoordinates d → ℝ) => fun y =>
            RN N omega (n i) (fun z => f i z * q z) y)
          (fun _ : SpatialCoordinates d => (1 : ℝ))) x := by
        simpa [P] using! houter

end Paper

