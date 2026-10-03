module

public import SubdiffusiveProcess.Section10.KilledKernelSmoothing

@[expose] public section

/-! Every-start continuity of the actual killed transition masses.
Whole-space strong Feller smooths the remaining killed mass. The exact
short-exit estimate makes these continuous smoothings locally uniform
approximations on compact interior neighborhoods, for every open domain.
-/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Section10

/-- Local L¹ approximation and uniform early exit imply continuity of
every actual killed transition mass at every interior starting point. -/
theorem continuousOn_killedKernel_of_localL1_and_early {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset NNReal,
      K.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (μ : Measure (Vec d)) (happrox : LocalL1ApproximationBound P μ)
    (hearly : UniformEarlyExit K) (U : Set (Vec d)) (hU : IsOpen U)
    (t : NNReal) (ht : 0 < t) (B : Set (Vec d)) (hB : MeasurableSet B) :
    ContinuousOn (fun x => (killedKernel (K.map LifetimePath.ofContinuousPath) U hU t x B).toReal) U := by
  let law := K.map LifetimePath.ofContinuousPath
  letI : IsMarkovKernel law := Kernel.IsMarkovKernel.map K LifetimePath.measurable_ofContinuousPath
  apply continuousOn_of_locally_uniform_approx_of_continuousWithinAt
  intro x hx V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let S := Metric.closedBall x (ρ / 2)
  have hS : IsCompact S := isCompact_closedBall x (ρ / 2)
  have hSU : S ⊆ U := by
    intro y hy
    apply hball
    exact (Metric.mem_closedBall.mp hy).trans_lt (half_lt_self hρ)
  have hSnhds : S ∈ 𝓝[U] x :=
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x (half_pos hρ))
  obtain ⟨δ, hδ, hexit⟩ := hearly U hU S hS hSU (ε / 2) (half_pos hε)
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  let s : NNReal := ⟨min ((t : ℝ) / 2) (δ / 2),
    le_of_lt (lt_min (half_pos htR) (half_pos hδ))⟩
  have hs : 0 < s := lt_min (half_pos htR) (half_pos hδ)
  have hsδ : (s : ℝ) < δ :=
    (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hst : s < t :=
    (min_le_left _ _).trans_lt (half_lt_self htR)
  let r := t - s
  have hsr : s + r = t := add_tsub_cancel_of_le hst.le
  let q : Vec d → ℝ := fun y => (killedKernel law U hU r y B).toReal
  have hq : Measurable q := ((killedKernel law U hU r).measurable_coe hB).ennreal_toReal
  have hqbound : ∀ y, |q y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top ENNReal.one_ne_top ((killedKernel_subMarkov law U hU r).measure_le_one y B))
      ENNReal.one_ne_top).2 ((killedKernel_subMarkov law U hU r).measure_le_one y B)
  have hu : Continuous (kernelIntegral (P s) q) :=
    continuous_kernelIntegral_of_localL1 P hFeller μ happrox s hs hq (by norm_num) hqbound
  refine ⟨S, hSnhds, kernelIntegral (P s) q, hu.continuousOn.continuousWithinAt hx, ?_⟩
  intro y hy
  apply hεV
  rw [Real.dist_eq]
  have herr := abs_killed_smoothing_error_le_exit P hP hFeller K hfdd U hU s r y B hB
  rw [hsr] at herr
  have hmass : (K y {w | ContinuousPath.exitTime U w ≤ (s : ENNReal)}).toReal ≤ ε / 2 := by
    calc
      _ ≤ (ENNReal.ofReal (ε / 2)).toReal :=
        (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2
          (hexit s hsδ y hy)
      _ = ε / 2 := ENNReal.toReal_ofReal (half_pos hε).le
  exact (herr.trans hmass).trans_lt (half_lt_self hε)

/-- The exact weighted-route supplier, for the original physical Feller
realization, its exact FDDs, and the independently supplied certificates. -/
theorem fellerKilledStartContinuitySupplier : FellerKilledStartContinuitySupplier := by
  intro d a _hapos _ha P hP hF K hK hfdd happrox hearly U hU t ht B hB
  letI : IsMarkovKernel K := hK
  have hfdd' : ∀ I : Finset NNReal,
      K.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I := by
    intro I
    ext x E hE
    exact congrArg (fun ν : Measure (I → Vec d) => ν E) (hfdd I x)
  exact continuousOn_killedKernel_of_localL1_and_early P hP hF K hfdd'
    (weightedMeasure a) happrox hearly U hU (Real.toNNReal t) (Real.toNNReal_pos.mpr ht) B hB

end SubdiffusiveProcess.Section10
