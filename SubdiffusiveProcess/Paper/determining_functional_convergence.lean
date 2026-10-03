module

public import SubdiffusiveProcess.Paper.lem_random_input
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
public import SubdiffusiveProcess.Paper.determining_functional_identity
public import SubdiffusiveProcess.Paper.tight_whole_space_resolvent_limit
public import SubdiffusiveProcess.Paper.in_crossing

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

namespace Paper


section
open Topology

/-- The one-time marginal of a finite-set kernel at a singleton time is the transition
kernel at that time. -/
theorem aux_determining_functional_convergence_singleton_marginal
    {α : Type*} [MeasurableSpace α] (P : SubMarkovKernelSemigroup α) (t : ℝ≥0) (x : α) :
    (SubMarkovKernelSemigroup.finiteSetKernel P {t} x).map
      (fun y : ({t} : Finset ℝ≥0) → α => y ⟨t, Finset.mem_singleton_self t⟩) = P t x := by
  have hmo := SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet
    (α := α) ({t} : Finset ℝ≥0)
  rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map, Kernel.map_apply _ hmo,
    Measure.map_map (measurable_pi_apply _) hmo]
  have hcomp : ((fun y : ({t} : Finset ℝ≥0) → α => y ⟨t, Finset.mem_singleton_self t⟩) ∘
      SubMarkovKernelSemigroup.orderedPathToFiniteSet ({t} : Finset ℝ≥0)) =
      fun path : Fin 1 → α => path 0 := by
    funext path
    simp only [Function.comp_apply, SubMarkovKernelSemigroup.orderedPathToFiniteSet]
    congr 1
    apply Fin.ext
    have hlt := ((({t} : Finset ℝ≥0).orderIsoOfFin rfl).symm
      ⟨t, Finset.mem_singleton_self t⟩).isLt
    have hc : ({t} : Finset ℝ≥0).card = 1 := rfl
    change _ = 0
    omega
  rw [hcomp]
  obtain ⟨τ, hτ⟩ : ∃ τ : FiniteOrderedTimes 1,
      τ = SubMarkovKernelSemigroup.finiteSetTimes ({t} : Finset ℝ≥0) := ⟨_, rfl⟩
  have h1 := SubMarkovKernelSemigroup.finiteTimeKernel_one_map_eval P τ
  have hmem : τ 0 = t := by
    rw [hτ]
    exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ _)
  rw [hmem] at h1
  have h2 := DFunLike.congr_fun h1 x
  rw [Kernel.map_apply _ (measurable_pi_apply 0)] at h2
  rw [← hτ]
  exact h2

/-- The in-crossing finite-dimensional identity gives the one-time marginals of the
path law. -/
theorem aux_determining_functional_convergence_marginal
    {d : ℕ} (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (x : SpatialCoordinates d)
    (κ : Measure (DiffusionPath d))
    (hmap : ∀ I : Finset ℝ≥0, κ.map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (t : ℝ≥0) :
    κ.map (fun path : DiffusionPath d => path t) = P t x := by
  have heval : Measurable (ContinuousPath.finsetEvaluation
      (alpha := SpatialCoordinates d) ({t} : Finset ℝ≥0)) := by
    rw [measurable_pi_iff]
    intro s
    exact ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d)
      (s : NNReal)
  have h := congrArg (fun ν : Measure (({t} : Finset ℝ≥0) → SpatialCoordinates d) =>
    ν.map (fun y => y ⟨t, Finset.mem_singleton_self t⟩)) (hmap {t})
  rw [aux_determining_functional_convergence_singleton_marginal, Measure.map_map
    (measurable_pi_apply _) heval] at h
  exact h

end

section
open Topology

theorem aux_determining_functional_convergence_exp_integral {m : ℝ} (hm : 0 < m) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-m * t) = 1 / m := by
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hm) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- Localized bound for the discounted semigroup resolvent: a path law with the right
one-time marginals which charges `Aᶜ` by at most `δ`, where the paths of `A` stay in `K`
up to time `T`, sees only the values of the datum on `K`, up to `δ` and the tail after
`T`. -/
theorem aux_determining_functional_convergence_loc_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : SubMarkovKernelSemigroup α) (x : α) (κ : Measure β) [IsProbabilityMeasure κ]
    (ev : β → ℝ≥0 → α) (hev : ∀ t, Measurable fun b => ev b t)
    (hmarg : ∀ t : ℝ≥0, κ.map (fun b => ev b t) = P t x)
    {m : ℝ} (hm : 0 < m) {g : α → ℝ} (hg : Measurable g) {D η δ T : ℝ}
    (hη : 0 ≤ η) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hgD : ∀ y, |g y| ≤ D)
    (A : Set β) (hA : MeasurableSet A) (K : Set α)
    (hAK : ∀ b ∈ A, ∀ t : ℝ≥0, (t : ℝ) ≤ T → ev b t ∈ K)
    (hgη : ∀ y ∈ K, |g y| ≤ η) (hκA : κ Aᶜ ≤ ENNReal.ofReal δ) :
    |P.kernelResolventReal m g x| ≤
      (η + D * δ) / m + 2 * D * Real.exp (-(m * T) / 2) / m := by
  have hk : ∀ t : ℝ≥0, kernelIntegral (P t) g x = ∫ b, g (ev b t) ∂κ := by
    intro t
    unfold kernelIntegral
    rw [← hmarg t, integral_map (hev t).aemeasurable hg.aestronglyMeasurable]
  have hk1 : ∀ t : ℝ≥0, (t : ℝ) ≤ T → |kernelIntegral (P t) g x| ≤ η + D * δ := by
    intro t ht
    rw [hk t, ← Real.norm_eq_abs]
    have hint : Integrable (fun b => η + Aᶜ.indicator (fun _ => D) b) κ :=
      (integrable_const η).add ((integrable_const D).indicator hA.compl)
    have hreal : κ.real Aᶜ ≤ δ := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hδ hκA
    calc ‖∫ b, g (ev b t) ∂κ‖ ≤ ∫ b, (η + Aᶜ.indicator (fun _ => D) b) ∂κ := by
          refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun b => ?_)
          rw [Real.norm_eq_abs]
          by_cases hb : b ∈ A
          · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hb)]
            linarith [hgη _ (hAK b hb t ht)]
          · rw [Set.indicator_of_mem (Set.mem_compl hb)]
            linarith [hgD (ev b t)]
      _ = η + D * κ.real Aᶜ := by
          rw [integral_add (integrable_const η) ((integrable_const D).indicator hA.compl),
            integral_const, integral_indicator_const _ hA.compl]
          simp [smul_eq_mul, mul_comm]
      _ ≤ η + D * δ := by linarith [mul_le_mul_of_nonneg_left hreal hD]
  have hk2 : ∀ t : ℝ≥0, |kernelIntegral (P t) g x| ≤ D := by
    intro t
    rw [hk t, ← Real.norm_eq_abs]
    have := norm_integral_le_of_norm_le_const (μ := κ) (f := fun b => g (ev b t)) (C := D)
      (Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hgD _)
    simpa using this
  have hi1 := exp_neg_integrableOn_Ioi 0 hm
  have hi2 := exp_neg_integrableOn_Ioi 0 (half_pos hm)
  have hb_int : IntegrableOn (fun t : ℝ => Real.exp (-m * t) * (η + D * δ) +
      D * Real.exp (-(m * T) / 2) * Real.exp (-(m / 2) * t)) (Set.Ioi 0) :=
    (hi1.mul_const _).add (hi2.const_mul _)
  have hηDδ : 0 ≤ η + D * δ := by positivity
  unfold SubMarkovKernelSemigroup.kernelResolventReal
  rw [← Real.norm_eq_abs]
  calc ‖∫ t in Set.Ioi (0 : ℝ), Real.exp (-m * t) * kernelIntegral (P (Real.toNNReal t)) g x‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-m * t) * (η + D * δ) +
          D * Real.exp (-(m * T) / 2) * Real.exp (-(m / 2) * t)) := by
        refine norm_integral_le_of_norm_le hb_int ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have ht0 : 0 ≤ t := le_of_lt ht
        have h2 : 0 ≤ D * Real.exp (-(m * T) / 2) * Real.exp (-(m / 2) * t) := by positivity
        by_cases htT : t ≤ T
        · have h1 := hk1 (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht0]; exact htT)
          have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-m * t)).le
          linarith
        · push_neg at htT
          have h1 := hk2 (Real.toNNReal t)
          have hexp : Real.exp (-m * t) ≤
              Real.exp (-(m * T) / 2) * Real.exp (-(m / 2) * t) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have := mul_lt_mul_of_pos_left htT hm
            linarith
          have h0 : 0 ≤ Real.exp (-m * t) * (η + D * δ) :=
            mul_nonneg (Real.exp_pos _).le hηDδ
          have h4 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-m * t)).le
          have h5 := mul_le_mul_of_nonneg_right hexp hD
          nlinarith
    _ = (η + D * δ) / m + 2 * D * Real.exp (-(m * T) / 2) / m := by
        rw [integral_add (hi1.mul_const _) (hi2.const_mul _), integral_mul_const,
          integral_const_mul, aux_determining_functional_convergence_exp_integral hm,
          aux_determining_functional_convergence_exp_integral (half_pos hm)]
        field_simp

/-- The localized bound for the difference of two bounded data. -/
theorem aux_determining_functional_convergence_loc_diff
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : SubMarkovKernelSemigroup α) (x : α) (κ : Measure β) [IsProbabilityMeasure κ]
    (ev : β → ℝ≥0 → α) (hev : ∀ t, Measurable fun b => ev b t)
    (hmarg : ∀ t : ℝ≥0, κ.map (fun b => ev b t) = P t x)
    {m : ℝ} (hm : 0 < m) {g1 g2 : α → ℝ} (hg1 : Measurable g1) (hg2 : Measurable g2)
    {C η δ T : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hg1C : ∀ y, |g1 y| ≤ C) (hg2C : ∀ y, |g2 y| ≤ C)
    (A : Set β) (hA : MeasurableSet A) (K : Set α)
    (hAK : ∀ b ∈ A, ∀ t : ℝ≥0, (t : ℝ) ≤ T → ev b t ∈ K)
    (hgη : ∀ y ∈ K, |g1 y - g2 y| ≤ η) (hκA : κ Aᶜ ≤ ENNReal.ofReal δ) :
    |P.kernelResolventReal m g1 x - P.kernelResolventReal m g2 x| ≤
      (η + 2 * C * δ) / m + 2 * (2 * C) * Real.exp (-(m * T) / 2) / m := by
  have hdiff : ∀ y, |(g1 - g2) y| ≤ 2 * C := by
    intro y
    have h1 := abs_le.mp (hg1C y)
    have h2 := abs_le.mp (hg2C y)
    simp only [Pi.sub_apply]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hadd := P.kernelResolventReal_add hm (hg1.sub hg2) hg2 hdiff hg2C
  have hsum : g1 - g2 + g2 = g1 := sub_add_cancel _ _
  rw [hsum] at hadd
  have hx := congrFun hadd x
  simp only [Pi.add_apply] at hx
  rw [hx, add_sub_cancel_right]
  exact aux_determining_functional_convergence_loc_bound P x κ ev hev hmarg hm (hg1.sub hg2)
    hη (by positivity) hδ hdiff A hA K hAK (fun y hy => by simpa using hgη y hy) hκA

/-- A countable family of bounded continuous functions, uniformly bounded by `C`, which
approximates every continuous function bounded by `C` uniformly on every compact set. -/
theorem aux_determining_functional_convergence_dense_family
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.SeparableSpace C(X, ℝ)]
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ φ : ℕ → BoundedContinuousFunction X ℝ, (∀ j y, |φ j y| ≤ C) ∧
      ∀ g : C(X, ℝ), (∀ y, |g y| ≤ C) → ∀ K : Set X, IsCompact K → ∀ η : ℝ, 0 < η →
        ∃ j, ∀ y ∈ K, |g y - φ j y| ≤ η := by
  obtain ⟨ψ, hψ⟩ := TopologicalSpace.exists_dense_seq C(X, ℝ)
  let clip : ℝ → ℝ := fun a => max (-C) (min C a)
  have hclip_cont : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  have hclip_bd : ∀ a, |clip a| ≤ C := fun a =>
    abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hclip_lip : ∀ a b, |clip a - clip b| ≤ |a - b| := by
    intro a b
    have h1 : |min C a - min C b| ≤ |a - b| := by
      simpa using abs_min_sub_min_le_max C a C b
    have h2 : |max (-C) (min C a) - max (-C) (min C b)| ≤ |min C a - min C b| := by
      simpa using abs_max_sub_max_le_max (-C) (min C a) (-C) (min C b)
    exact h2.trans h1
  have hclip_fix : ∀ a, |a| ≤ C → clip a = a := by
    intro a ha
    have h := abs_le.mp ha
    simp only [clip, min_eq_right h.2, max_eq_right h.1]
  let φ : ℕ → BoundedContinuousFunction X ℝ := fun j =>
    BoundedContinuousFunction.mkOfBound ⟨fun y => clip (ψ j y), hclip_cont.comp (ψ j).continuous⟩
      (2 * C) (fun y z => by
        rw [Real.dist_eq]
        have h1 := abs_le.mp (hclip_bd (ψ j y))
        have h2 := abs_le.mp (hclip_bd (ψ j z))
        exact abs_le.mpr ⟨by simp only [ContinuousMap.coe_mk]; linarith,
          by simp only [ContinuousMap.coe_mk]; linarith⟩)
  refine ⟨φ, fun j y => hclip_bd _, fun g hg K hK η hη => ?_⟩
  have hE : {fg : C(X, ℝ) × C(X, ℝ) | ∀ y ∈ K, (fg.1 y, fg.2 y) ∈
      {p : ℝ × ℝ | dist p.1 p.2 < η}} ∈ uniformity C(X, ℝ) :=
    ContinuousMap.hasBasis_compactConvergenceUniformity.mem_of_mem
      (i := (K, {p : ℝ × ℝ | dist p.1 p.2 < η})) ⟨hK, Metric.dist_mem_uniformity hη⟩
  have hU := UniformSpace.ball_mem_nhds g hE
  obtain ⟨j, hj⟩ := hψ.mem_nhds hU
  refine ⟨j, fun y hy => ?_⟩
  have h1 : dist (g y) (ψ j y) < η := hj y hy
  rw [Real.dist_eq] at h1
  have h2 := hclip_lip (g y) (ψ j y)
  rw [hclip_fix (g y) (hg y)] at h2
  change |g y - clip (ψ j y)| ≤ η
  linarith

/-- Finitely many members of an approximating family suffice with high probability. -/
theorem aux_determining_functional_convergence_choose_J
    {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X] (μ : Measure Ω) [IsFiniteMeasure μ]
    (u w : Ω → X → ℝ) (hw : ∀ y, Measurable fun ω => w ω y)
    (huw : ∀ᵐ ω ∂μ, u ω = w ω) (hu : ∀ᵐ ω ∂μ, Continuous (u ω))
    (φ : ℕ → X → ℝ) (hφc : ∀ j, Continuous (φ j)) (K : Set X) (hK : IsCompact K) {η : ℝ}
    (hdense : ∀ᵐ ω ∂μ, ∃ j, ∀ y ∈ K, |u ω y - φ j y| ≤ η) {r : ℝ} (hr : 0 < r) :
    ∃ J : ℕ, μ {ω | ¬ ∃ j < J, ∀ y ∈ K, |u ω y - φ j y| ≤ η} ≤ ENNReal.ofReal r := by
  obtain ⟨D, hDK, hDc, hKD⟩ := hK.isSeparable.exists_countable_dense_subset
  let S : ℕ → Set Ω := fun J => {ω | ∃ j < J, ∀ y ∈ D, |w ω y - φ j y| ≤ η}
  have hSm : ∀ J, MeasurableSet (S J) := by
    intro J
    have : S J = ⋃ j ∈ Finset.range J, ⋂ y ∈ D, {ω | |w ω y - φ j y| ≤ η} := by
      ext ω; simp [S, Finset.mem_range]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun j _ => MeasurableSet.biInter hDc fun y _ =>
      measurableSet_le ((continuous_abs.measurable).comp ((hw y).sub measurable_const))
        measurable_const
  have hSmono : Monotone S := fun J J' hJ ω ⟨j, hj, h⟩ => ⟨j, lt_of_lt_of_le hj hJ, h⟩
  let Z : Set Ω := {ω | ¬ (u ω = w ω ∧ Continuous (u ω) ∧ ∃ j, ∀ y ∈ K, |u ω y - φ j y| ≤ η)}
  have hZ : μ Z = 0 := by
    have : ∀ᵐ ω ∂μ, u ω = w ω ∧ Continuous (u ω) ∧ ∃ j, ∀ y ∈ K, |u ω y - φ j y| ≤ η := by
      filter_upwards [huw, hu, hdense] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
    exact ae_iff.mp this
  have hsub1 : ∀ J, {ω | ¬ ∃ j < J, ∀ y ∈ K, |u ω y - φ j y| ≤ η} ⊆ (S J)ᶜ ∪ Z := by
    intro J ω hω
    by_contra hc
    rw [Set.mem_union, not_or, Set.mem_compl_iff, not_not] at hc
    obtain ⟨⟨j, hj, hjD⟩, hZω⟩ := hc
    have hZω' : u ω = w ω ∧ Continuous (u ω) ∧ ∃ j, ∀ y ∈ K, |u ω y - φ j y| ≤ η := by
      by_contra h; exact hZω h
    obtain ⟨huw', hcont, -⟩ := hZω'
    apply hω
    refine ⟨j, hj, ?_⟩
    have hclosed : IsClosed {y | |u ω y - φ j y| ≤ η} :=
      isClosed_le ((hcont.sub (hφc j)).abs) continuous_const
    have hDsub : D ⊆ {y | |u ω y - φ j y| ≤ η} := fun y hy => by
      simp only [Set.mem_setOf_eq]; rw [huw']; exact hjD y hy
    exact fun y hy => (closure_minimal hDsub hclosed) (hKD hy)
  have hsub2 : (⋂ J, (S J)ᶜ) ⊆ Z := by
    intro ω hω
    by_contra hZω
    have hZω' : u ω = w ω ∧ Continuous (u ω) ∧ ∃ j, ∀ y ∈ K, |u ω y - φ j y| ≤ η := by
      by_contra h; exact hZω h
    obtain ⟨huw', -, j, hj⟩ := hZω'
    have := Set.mem_iInter.mp hω (j + 1)
    apply this
    exact ⟨j, Nat.lt_succ_self j, fun y hy => by rw [← huw']; exact hj y (hDK hy)⟩
  have hanti : Antitone fun J => (S J)ᶜ := fun J J' h => Set.compl_subset_compl.mpr (hSmono h)
  have hinf : ⨅ J, μ (S J)ᶜ = 0 := by
    rw [← hanti.measure_iInter (fun J => (hSm J).compl.nullMeasurableSet)
      ⟨0, measure_ne_top μ _⟩]
    exact measure_mono_null hsub2 hZ
  have hlt : ⨅ J, μ (S J)ᶜ < ENNReal.ofReal r := by
    rw [hinf]; exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨J, hJ⟩ := iInf_lt_iff.mp hlt
  refine ⟨J, ?_⟩
  calc μ {ω | ¬ ∃ j < J, ∀ y ∈ K, |u ω y - φ j y| ≤ η} ≤ μ ((S J)ᶜ ∪ Z) :=
        measure_mono (hsub1 J)
    _ ≤ μ (S J)ᶜ + μ Z := measure_union_le _ _
    _ ≤ ENNReal.ofReal r := by rw [hZ, add_zero]; exact hJ.le

/-- Choice of the time horizon. -/
theorem aux_determining_functional_convergence_choose_T {C β m : ℝ} (hC : 0 ≤ C)
    (hβ : 0 < β) (hm : 0 < m) :
    ∃ T : ℝ, 0 ≤ T ∧ 2 * (2 * C) * Real.exp (-(m * T) / 2) ≤ β := by
  refine ⟨2 * (4 * C / β) / m, by positivity, ?_⟩
  have hy : -(m * (2 * (4 * C / β) / m)) / 2 = -(4 * C / β) := by
    field_simp
  rw [hy]
  have hy0 : 0 ≤ 4 * C / β := by positivity
  have hE := Real.exp_pos (-(4 * C / β))
  have hexp : Real.exp (-(4 * C / β)) * (1 + 4 * C / β) ≤ 1 := by
    have h1 := Real.add_one_le_exp (4 * C / β)
    calc Real.exp (-(4 * C / β)) * (1 + 4 * C / β)
        ≤ Real.exp (-(4 * C / β)) * Real.exp (4 * C / β) :=
          mul_le_mul_of_nonneg_left (by linarith) hE.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have h2 : Real.exp (-(4 * C / β)) * (4 * C / β) ≤ 1 := by nlinarith
  have h3 : Real.exp (-(4 * C / β)) * (4 * C / β) * β = Real.exp (-(4 * C / β)) * (4 * C) := by
    field_simp
  have h4 := mul_le_mul_of_nonneg_right h2 hβ.le
  rw [h3, one_mul] at h4
  linarith

end

section DeterminingFunctionalConvergenceCapacity

open Set Topology

/-! #### Capacity -/
/-- One step of the capacitability construction: cutting the `k`-th coordinate at a finite
bound loses arbitrarily little outer measure of the image. -/
theorem aux_determining_functional_convergence_cut_step {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : (ℕ → ℕ) → α) (S : Set (ℕ → ℕ)) (k : ℕ)
    {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ b : ℕ, μ (f '' S) ≤ μ (f '' (S ∩ {s | s k ≤ b})) + η := by
  have hunion : f '' S = ⋃ b : ℕ, f '' (S ∩ {s | s k ≤ b}) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact mem_iUnion.2 ⟨s k, s, ⟨hs, (le_rfl : s k ≤ s k)⟩, rfl⟩
    · intro hy
      obtain ⟨b, s, hs, rfl⟩ := mem_iUnion.1 hy
      exact ⟨s, hs.1, rfl⟩
  have hmono : Monotone (fun b : ℕ => f '' (S ∩ {s | s k ≤ b})) := by
    intro b b' hbb'
    exact image_mono (inter_subset_inter_right _ (fun s (hs : s k ≤ b) => le_trans hs hbb'))
  have hsup : μ (f '' S) = ⨆ b : ℕ, μ (f '' (S ∩ {s | s k ≤ b})) := by
    rw [hunion]
    exact hmono.measure_iUnion
  by_contra hcon
  push_neg at hcon
  have hfin : μ (f '' S) ≠ ∞ := measure_ne_top μ _
  have hpos : μ (f '' S) ≠ 0 := by
    have := hcon 0
    exact (lt_of_le_of_lt zero_le this).ne'
  have hle : μ (f '' S) ≤ μ (f '' S) - η := by
    conv_lhs => rw [hsup]
    refine iSup_le fun b => ?_
    exact ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top hfin
      (le_add_self.trans (hcon b).le)) (hcon b).le
  exact absurd hle (not_le.2 (ENNReal.sub_lt_self hfin hpos hη))

/-- The compactness step of capacitability: points in the closures of all truncated images
lie in the image of the limiting compact box. -/
theorem aux_determining_functional_convergence_closure_box {α : Type*} [TopologicalSpace α] [T2Space α]
    [TopologicalSpace.PseudoMetrizableSpace α] (f : (ℕ → ℕ) → α) (hf : Continuous f)
    (m : ℕ → ℕ) (y : α)
    (hy : ∀ n : ℕ, y ∈ closure (f '' {s : ℕ → ℕ | ∀ i < n, s i ≤ m i})) :
    y ∈ f '' {s : ℕ → ℕ | ∀ i, s i ≤ m i} := by
  letI := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
  have hchoose : ∀ n : ℕ, ∃ s : ℕ → ℕ, (∀ i < n, s i ≤ m i) ∧
      dist (f s) y < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 (hy n) _ hpos
    obtain ⟨s, hs, rfl⟩ := hb
    exact ⟨s, hs, by rwa [dist_comm]⟩
  choose s hs hsd using hchoose
  let u : ℕ → ℕ → ℕ := fun n i => min (s n i) (m i)
  have hLc : IsCompact {s : ℕ → ℕ | ∀ i, s i ≤ m i} := by
    have : {s : ℕ → ℕ | ∀ i, s i ≤ m i} = Set.pi univ (fun i => Iic (m i)) := by
      ext s; simp only [mem_setOf_eq, Set.mem_pi, mem_univ, mem_Iic, true_implies]
    rw [this]
    exact isCompact_univ_pi fun i => (Set.finite_Iic (m i)).isCompact
  have huL : ∀ n, u n ∈ {s : ℕ → ℕ | ∀ i, s i ≤ m i} := fun n i => min_le_right _ _
  obtain ⟨a, haL, φ, hφ, hlim⟩ := hLc.tendsto_subseq huL
  have hslim : Tendsto (fun j => s (φ j)) atTop (𝓝 a) := by
    rw [tendsto_pi_nhds]
    intro i
    have hu_i : Tendsto (fun j => u (φ j) i) atTop (𝓝 (a i)) :=
      ((continuous_apply i).tendsto a).comp hlim
    refine hu_i.congr' ?_
    filter_upwards [eventually_ge_atTop (i + 1)] with j hj
    have hij : i < φ j := lt_of_lt_of_le (Nat.lt_of_succ_le hj) (hφ.id_le j)
    exact min_eq_left (hs (φ j) i hij)
  have hf1 : Tendsto (fun j => f (s (φ j))) atTop (𝓝 (f a)) :=
    (hf.tendsto a).comp hslim
  have hf2 : Tendsto (fun j => f (s (φ j))) atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) h0
    refine (hsd (φ j)).le.trans ?_
    have : (j : ℝ) ≤ φ j := by exact_mod_cast hφ.id_le j
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  exact ⟨a, haL, tendsto_nhds_unique hf1 hf2⟩

/-- Inner approximation of an analytic set by closed subsets, up to arbitrarily small outer
measure. -/
theorem aux_determining_functional_convergence_analytic_inner {α : Type*} [TopologicalSpace α]
    [T2Space α] [TopologicalSpace.PseudoMetrizableSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : (ℕ → ℕ) → α) (hf : Continuous f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ L : Set α, IsClosed L ∧ L ⊆ range f ∧ μ (range f) ≤ μ L + ε := by
  classical
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε ℕ
  have hstep : ∀ (S : Set (ℕ → ℕ)) (k : ℕ), ∃ b : ℕ,
      μ (f '' S) ≤ μ (f '' (S ∩ {s | s k ≤ b})) + (ε' k : ℝ≥0∞) := fun S k =>
    aux_determining_functional_convergence_cut_step μ f S k
      (by exact_mod_cast (hε'pos k).ne')
  choose bsel hbsel using hstep
  let D : ℕ → Set (ℕ → ℕ) := fun n =>
    Nat.rec (motive := fun _ => Set (ℕ → ℕ)) univ
      (fun k Dk => Dk ∩ {s | s k ≤ bsel Dk k}) n
  have hDsucc : ∀ k, D (k + 1) = D k ∩ {s | s k ≤ bsel (D k) k} := fun k => rfl
  let m : ℕ → ℕ := fun i => bsel (D i) i
  have hDeq : ∀ n, D n = {s : ℕ → ℕ | ∀ i < n, s i ≤ m i} := by
    intro n
    induction n with
    | zero => ext s; simp [D]
    | succ k ih =>
      rw [hDsucc, ih]
      ext s
      simp only [mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h1 i hi
        · simpa [m, ih] using h2
      · intro h
        refine ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), ?_⟩
        have := h k (Nat.lt_succ_self k)
        simpa [m, ih] using this
  have hbound : ∀ n, μ (range f) ≤ μ (f '' D n) + ∑ i ∈ Finset.range n, (ε' i : ℝ≥0∞) := by
    intro n
    induction n with
    | zero => simp [D, image_univ]
    | succ k ih =>
      rw [Finset.sum_range_succ, hDsucc]
      calc μ (range f) ≤ μ (f '' D k) + ∑ i ∈ Finset.range k, (ε' i : ℝ≥0∞) := ih
        _ ≤ (μ (f '' (D k ∩ {s | s k ≤ bsel (D k) k})) + (ε' k : ℝ≥0∞)) +
              ∑ i ∈ Finset.range k, (ε' i : ℝ≥0∞) := by gcongr; exact hbsel (D k) k
        _ = _ := by ring
  have hsum_le : ∀ n, ∑ i ∈ Finset.range n, (ε' i : ℝ≥0∞) ≤ ε := fun n =>
    (ENNReal.sum_le_tsum _).trans hε'sum.le
  let L : Set α := f '' {s : ℕ → ℕ | ∀ i, s i ≤ m i}
  have hLc : IsCompact {s : ℕ → ℕ | ∀ i, s i ≤ m i} := by
    have : {s : ℕ → ℕ | ∀ i, s i ≤ m i} = Set.pi univ (fun i => Iic (m i)) := by
      ext s; simp only [mem_setOf_eq, Set.mem_pi, mem_univ, mem_Iic, true_implies]
    rw [this]
    exact isCompact_univ_pi fun i => (Set.finite_Iic (m i)).isCompact
  have hLclosed : IsClosed L := (hLc.image hf).isClosed
  refine ⟨L, hLclosed, image_subset_range _ _, ?_⟩
  -- the closures of the truncated images decrease to a subset of `L`
  let C : ℕ → Set α := fun n => closure (f '' D n)
  have hCanti : Antitone C := by
    intro n n' hnn'
    refine closure_mono (image_mono ?_)
    rw [hDeq, hDeq]
    intro s hs i hi
    exact hs i (lt_of_lt_of_le hi hnn')
  have hCsub : (⋂ n, C n) ⊆ L := by
    intro y hy
    refine aux_determining_functional_convergence_closure_box f hf m y (fun n => ?_)
    have := mem_iInter.1 hy n
    simpa [C, hDeq n] using this
  have hmeasC : μ (⋂ n, C n) = ⨅ n, μ (C n) :=
    hCanti.measure_iInter (fun n => isClosed_closure.measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top μ _⟩
  calc μ (range f) ≤ ⨅ n, (μ (C n) + ε) := by
        refine le_iInf fun n => ?_
        calc μ (range f) ≤ μ (f '' D n) + ∑ i ∈ Finset.range n, (ε' i : ℝ≥0∞) := hbound n
          _ ≤ μ (C n) + ε := add_le_add (measure_mono subset_closure) (hsum_le n)
    _ = μ (⋂ n, C n) + ε := by rw [← ENNReal.iInf_add, hmeasC]
    _ ≤ μ L + ε := by gcongr

/-- **Analytic sets are null-measurable** for every finite Borel measure on a metrizable
Hausdorff space (the capacitability argument). -/
theorem aux_determining_functional_convergence_analytic_nullMeasurable {α : Type*}
    [TopologicalSpace α] [T2Space α] [TopologicalSpace.PseudoMetrizableSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {A : Set α} (hA : AnalyticSet A) : NullMeasurableSet A μ := by
  rw [AnalyticSet_def] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · exact nullMeasurableSet_empty
  have hchoose : ∀ n : ℕ, ∃ L : Set α, IsClosed L ∧ L ⊆ range f ∧
      μ (range f) ≤ μ L + ((n : ℝ≥0∞) + 1)⁻¹ := fun n =>
    aux_determining_functional_convergence_analytic_inner μ f hf (by simp)
  choose L hLc hLsub hLμ using hchoose
  let U : Set α := ⋃ n, L n
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun n => (hLc n).measurableSet
  have hUsub : U ⊆ range f := iUnion_subset hLsub
  have hle : μ (range f) ≤ μ U := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
    calc μ (range f) ≤ μ (L n) + ((n : ℝ≥0∞) + 1)⁻¹ := hLμ n
      _ ≤ μ U + ε := by
        gcongr
        · exact subset_iUnion L n
        · refine le_trans ?_ hn.le
          exact ENNReal.inv_le_inv.2 (le_self_add)
  have hdiff : μ (range f \ U) = 0 := by
    have hsplit := measure_inter_add_diff (range f) hUm (μ := μ)
    rw [inter_eq_right.2 hUsub] at hsplit
    have hfin : μ U ≠ ∞ := measure_ne_top μ _
    have : μ (range f \ U) ≤ 0 := by
      have h1 : μ U + μ (range f \ U) ≤ μ U + 0 := by
        rw [hsplit, add_zero]; exact hle
      exact (ENNReal.add_le_add_iff_left hfin).1 h1
    exact le_antisymm this zero_le
  have : range f = U ∪ (range f \ U) := (union_diff_cancel hUsub).symm
  rw [this]
  exact hUm.nullMeasurableSet.union (NullMeasurableSet.of_null hdiff)

/-- Markov's inequality for an uncountable-supremum event.  The event `∃ x ∈ B, c < F (ω, x)`
is the projection of a Borel set of a Polish product, hence analytic, hence null-measurable;
so its outer measure is controlled by the (lower) integral of the supremum. -/
theorem aux_determining_functional_convergence_markov_sup {Ω X : Type*}
    [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω × X → ℝ≥0∞) (hF : Measurable F)
    (B : Set X) (hB : MeasurableSet B) (c : ℝ≥0∞) :
    c * μ {ω | ∃ x ∈ B, c < F (ω, x)} ≤ ∫⁻ ω, ⨆ x ∈ B, F (ω, x) ∂μ := by
  set A := {ω | ∃ x ∈ B, c < F (ω, x)} with hAdef
  have hS : MeasurableSet {p : Ω × X | p.2 ∈ B ∧ c < F p} :=
    (measurable_snd hB).inter (measurableSet_lt measurable_const hF)
  have hAeq : A = Prod.fst '' {p : Ω × X | p.2 ∈ B ∧ c < F p} := by
    ext ω; constructor
    · rintro ⟨x, hx, hc⟩; exact ⟨(ω, x), ⟨hx, hc⟩, rfl⟩
    · rintro ⟨⟨ω', x⟩, ⟨hx, hc⟩, rfl⟩; exact ⟨x, hx, hc⟩
  have hAan : AnalyticSet A := by
    rw [hAeq]; exact (hS.analyticSet).image_of_continuous continuous_fst
  have hAnull := aux_determining_functional_convergence_analytic_nullMeasurable μ hAan
  obtain ⟨T, hTA, hTm, hTae⟩ := hAnull.exists_measurable_subset_ae_eq
  rw [← measure_congr hTae, ← lintegral_indicator_const hTm c]
  refine lintegral_mono fun ω => ?_
  by_cases hω : ω ∈ T
  · rw [indicator_of_mem hω]
    obtain ⟨x, hx, hc⟩ := hTA hω
    exact hc.le.trans (le_iSup₂ (f := fun x (_ : x ∈ B) => F (ω, x)) x hx)
  · rw [indicator_of_notMem hω]; exact zero_le

theorem aux_determining_functional_convergence_tight_event {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d)) [IsProbabilityMeasure μ]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (B : Set (SpatialCoordinates d)) (hB : IsCompact B) (Kset : Set (DiffusionPath d))
    (hKset : IsCompact Kset) {δ r : ℝ} (hδ : 0 < δ)
    (hint : (∫⁻ omega, ⨆ x ∈ B, (K (omega, x)) Ksetᶜ ∂μ) ≤ ENNReal.ofReal (r * δ)) :
    μ {omega | ∃ x ∈ B, ENNReal.ofReal δ < K (omega, x) Ksetᶜ} ≤ ENNReal.ofReal r := by
  haveI : PolishSpace (BilateralField d) := {}
  have hF : Measurable (fun q : BilateralField d × SpatialCoordinates d => K q Ksetᶜ) :=
    K.measurable_coe hKset.isClosed.measurableSet.compl
  have hM := aux_determining_functional_convergence_markov_sup μ
    (fun q : BilateralField d × SpatialCoordinates d => K q Ksetᶜ) hF B
    hB.isClosed.measurableSet (ENNReal.ofReal δ)
  have h2 : ENNReal.ofReal δ * μ {omega | ∃ x ∈ B, ENNReal.ofReal δ < K (omega, x) Ksetᶜ} ≤
      ENNReal.ofReal δ * ENNReal.ofReal r := by
    refine hM.trans (hint.trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_mul hδ.le, mul_comm]
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top).1 h2

end DeterminingFunctionalConvergenceCapacity

section
open Topology

/-- The five-term comparison at one environment and one starting point. -/
theorem aux_determining_functional_convergence_step_point
    {d : ℕ} (P P' : SubMarkovKernelSemigroup (SpatialCoordinates d)) (x : SpatialCoordinates d)
    (κ κ' : Measure (DiffusionPath d)) [IsProbabilityMeasure κ] [IsProbabilityMeasure κ']
    (hmarg : ∀ t : ℝ≥0, κ.map (fun path : DiffusionPath d => path t) = P t x)
    (hmarg' : ∀ t : ℝ≥0, κ'.map (fun path : DiffusionPath d => path t) = P' t x)
    {m : ℝ} (hm : 0 < m) (a b c a' : SpatialCoordinates d → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (ha' : Measurable a')
    {C β δ T eps : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (haC : ∀ y, |a y| ≤ C) (hbC : ∀ y, |b y| ≤ C) (hcC : ∀ y, |c y| ≤ C)
    (ha'C : ∀ y, |a' y| ≤ C)
    (A : Set (DiffusionPath d)) (hA : MeasurableSet A) (K : Set (SpatialCoordinates d))
    (hAK : ∀ path ∈ A, ∀ t : ℝ≥0, (t : ℝ) ≤ T → path t ∈ K)
    (hκA : κ Aᶜ ≤ ENNReal.ofReal δ) (hκA' : κ' Aᶜ ≤ ENNReal.ofReal δ)
    (hab : ∀ y ∈ K, |a y - b y| ≤ β) (ha'b : ∀ y ∈ K, |a' y - b y| ≤ β)
    (hbc : ∀ y ∈ K, |b y - c y| ≤ β)
    (hdetx : |P.kernelResolventReal m c x - P'.kernelResolventReal m c x| < eps / 5)
    (hbudget : (β + 2 * C * δ) / m + 2 * (2 * C) * Real.exp (-(m * T) / 2) / m ≤ eps / 5) :
    |P.kernelResolventReal m a x - P'.kernelResolventReal m a' x| < eps := by
  have hev : ∀ t : ℝ≥0, Measurable fun path : DiffusionPath d => path t := fun t =>
    ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) t
  have e1 := aux_determining_functional_convergence_loc_diff P x κ (fun p t => p t) hev hmarg
    hm ha hb hβ hC hδ haC hbC A hA K hAK hab hκA
  have e2 := aux_determining_functional_convergence_loc_diff P x κ (fun p t => p t) hev hmarg
    hm hb hc hβ hC hδ hbC hcC A hA K hAK hbc hκA
  have e4 := aux_determining_functional_convergence_loc_diff P' x κ' (fun p t => p t) hev
    hmarg' hm hc hb hβ hC hδ hcC hbC A hA K hAK
    (fun y hy => by rw [abs_sub_comm]; exact hbc y hy) hκA'
  have e5 := aux_determining_functional_convergence_loc_diff P' x κ' (fun p t => p t) hev
    hmarg' hm hb ha' hβ hC hδ hbC ha'C A hA K hAK
    (fun y hy => by rw [abs_sub_comm]; exact ha'b y hy) hκA'
  have f1 := abs_le.mp (e1.trans hbudget)
  have f2 := abs_le.mp (e2.trans hbudget)
  have f4 := abs_le.mp (e4.trans hbudget)
  have f5 := abs_le.mp (e5.trans hbudget)
  have f3 := abs_lt.mp hdetx
  rw [abs_lt]
  constructor <;> linarith

theorem aux_determining_functional_convergence_arith (J : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ENNReal.ofReal (rho / 8) + ENNReal.ofReal (rho / 8) + ENNReal.ofReal (rho / 8) +
      ENNReal.ofReal (rho / 8) + ENNReal.ofReal (rho / 8) + 0 +
      (J : ℝ≥0∞) * ENNReal.ofReal (rho / (8 * ((J : ℝ) + 1))) ≤ ENNReal.ofReal rho := by
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  rw [add_zero, ← ENNReal.ofReal_natCast J, ← ENNReal.ofReal_mul hJ,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h : (J : ℝ) * (rho / (8 * ((J : ℝ) + 1))) ≤ rho / 8 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- **Random-input Cauchy step.**  If uniformly bounded, almost surely continuous random
data with measurable versions are Cauchy locally uniformly in probability, then so are
their discounted finite-cutoff resolvents.  This is the argument of the paper's random-input
lemma in Cauchy form: localization by tightness and discounting, then finitely many
deterministic data from a countable dense family and the deterministic-input Cauchy
property. -/
theorem aux_determining_functional_convergence_step
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d)) [IsProbabilityMeasure μ]
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hmarg : ∀ᵐ ω ∂μ, ∀ (N : ℕ) (x : SpatialCoordinates d) (t : ℝ≥0),
      (KN N (ω, x)).map (fun path : DiffusionPath d => path t) = PN N ω t x)
    (hdet : ∀ m : ℕ, 0 < m → ∀ φ : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
        μ {ω | ∃ x ∈ B, eps ≤ |(PN N ω).kernelResolventReal m φ x -
          (PN N' ω).kernelResolventReal m φ x|} ≤ ENNReal.ofReal rho)
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∃ A : Set (DiffusionPath d), IsCompact A ∧ ∀ N : ℕ,
        (∫⁻ ω, ⨆ x ∈ B, KN N (ω, x) Aᶜ ∂μ) ≤ ENNReal.ofReal eps)
    (m : ℕ) (hm : 0 < m) (h : ℕ → BilateralField d → SpatialCoordinates d → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ N ω y, |h N ω y| ≤ C)
    (hhc : ∀ᵐ ω ∂μ, ∀ N, Continuous (h N ω))
    (hver : ∀ N, ∃ w : BilateralField d → SpatialCoordinates d → ℝ,
      (∀ y, Measurable fun ω => w ω y) ∧ ∀ᵐ ω ∂μ, h N ω = w ω)
    (hcau : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
        μ {ω | ∃ x ∈ B, eps ≤ |h N ω x - h N' ω x|} ≤ ENNReal.ofReal rho) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
        μ {ω | ∃ x ∈ B, eps ≤ |(PN N ω).kernelResolventReal m (h N ω) x -
          (PN N' ω).kernelResolventReal m (h N' ω) x|} ≤ ENNReal.ofReal rho := by
  intro B hB eps heps rho hrho
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (m : ℝ) * eps / 15 := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβdef]; positivity
  obtain ⟨T, hT0, hTb⟩ := aux_determining_functional_convergence_choose_T hC hβ hm'
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = β / (2 * C + 1) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδb : 2 * C * δ ≤ β := by
    rw [hδdef, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hbudget : (β + 2 * C * δ) / (m : ℝ) + 2 * (2 * C) * Real.exp (-((m : ℝ) * T) / 2) /
      (m : ℝ) ≤ eps / 5 := by
    rw [← add_div, div_le_iff₀ hm']
    have : eps / 5 * (m : ℝ) = 3 * β := by rw [hβdef]; ring
    rw [this]
    linarith
  obtain ⟨ρ', hρ'def⟩ : ∃ ρ' : ℝ, ρ' = rho / 8 := ⟨_, rfl⟩
  have hρ' : 0 < ρ' := by rw [hρ'def]; positivity
  obtain ⟨A, hAc, hA⟩ := htight B hB (ρ' * δ) (by positivity)
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  let K' : Set (SpatialCoordinates d) :=
    (fun p : DiffusionPath d × ℝ≥0 => p.1 p.2) '' (A ×ˢ Set.Icc 0 T.toNNReal)
  have hK'c : IsCompact K' := (hAc.prod isCompact_Icc).image continuous_eval
  have hAK : ∀ path ∈ A, ∀ t : ℝ≥0, (t : ℝ) ≤ T → path t ∈ K' := by
    intro path hp t ht
    exact ⟨(path, t), ⟨hp, ⟨zero_le, (Real.le_toNNReal_iff_coe_le hT0).mpr ht⟩⟩, rfl⟩
  obtain ⟨M, hM⟩ := hcau K' hK'c β hβ ρ' hρ'
  obtain ⟨φ, hφb, hφd⟩ :=
    aux_determining_functional_convergence_dense_family (X := SpatialCoordinates d) C hC
  obtain ⟨w, hwm, hw⟩ := hver M
  have hdense : ∀ᵐ ω ∂μ, ∃ j, ∀ y ∈ K', |h M ω y - φ j y| ≤ β := by
    filter_upwards [hhc] with ω hω
    exact hφd ⟨h M ω, hω M⟩ (hbd M ω) K' hK'c β hβ
  obtain ⟨J, hJ⟩ := aux_determining_functional_convergence_choose_J μ (h M) w hwm hw
    (hhc.mono fun ω hω => hω M) (fun j => φ j) (fun j => (φ j).continuous) K' hK'c hdense hρ'
  have hdj : ∀ j : ℕ, ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
      μ {ω | ∃ x ∈ B, eps / 5 ≤ |(PN N ω).kernelResolventReal m (φ j) x -
        (PN N' ω).kernelResolventReal m (φ j) x|} ≤
        ENNReal.ofReal (rho / (8 * ((J : ℝ) + 1))) := fun j =>
    hdet m hm (φ j) B hB (eps / 5) (by positivity) _ (by positivity)
  choose Nd hNd using hdj
  refine ⟨M + ∑ j ∈ Finset.range J, Nd j, fun N N' hN hN' => ?_⟩
  have hMN : M ≤ N := le_trans (Nat.le_add_right _ _) hN
  have hMN' : M ≤ N' := le_trans (Nat.le_add_right _ _) hN'
  have hNdle : ∀ j ∈ Finset.range J, Nd j ≤ N ∧ Nd j ≤ N' := fun j hj =>
    ⟨le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj)
      (Nat.le_add_left _ _)) hN,
     le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj)
      (Nat.le_add_left _ _)) hN'⟩
  -- the exceptional events
  let Tt : ℕ → Set (BilateralField d) := fun L =>
    {ω | ∃ x ∈ B, ENNReal.ofReal δ < KN L (ω, x) Aᶜ}
  have hTt : ∀ L, μ (Tt L) ≤ ENNReal.ofReal ρ' := fun L =>
    aux_determining_functional_convergence_tight_event μ (KN L) B hB A hAc hδ (hA L)
  let Cau : ℕ → Set (BilateralField d) := fun L =>
    {ω | ∃ y ∈ K', β ≤ |h L ω y - h M ω y|}
  have hCauN : μ (Cau N) ≤ ENNReal.ofReal ρ' := hM N M hMN le_rfl
  have hCauN' : μ (Cau N') ≤ ENNReal.ofReal ρ' := hM N' M hMN' le_rfl
  let Jb : Set (BilateralField d) := {ω | ¬ ∃ j < J, ∀ y ∈ K', |h M ω y - φ j y| ≤ β}
  let Z : Set (BilateralField d) := {ω | ¬ ((∀ (L : ℕ) (x : SpatialCoordinates d) (t : ℝ≥0),
      (KN L (ω, x)).map (fun path : DiffusionPath d => path t) = PN L ω t x) ∧
      ∀ L, Continuous (h L ω))}
  have hZ : μ Z = 0 := by
    have : ∀ᵐ ω ∂μ, (∀ (L : ℕ) (x : SpatialCoordinates d) (t : ℝ≥0),
        (KN L (ω, x)).map (fun path : DiffusionPath d => path t) = PN L ω t x) ∧
        ∀ L, Continuous (h L ω) := by
      filter_upwards [hmarg, hhc] with ω h1 h2 using ⟨h1, h2⟩
    exact ae_iff.mp this
  let Det : Set (BilateralField d) := ⋃ j ∈ Finset.range J,
    {ω | ∃ x ∈ B, eps / 5 ≤ |(PN N ω).kernelResolventReal m (φ j) x -
      (PN N' ω).kernelResolventReal m (φ j) x|}
  have hDet : μ Det ≤ (J : ℝ≥0∞) * ENNReal.ofReal (rho / (8 * ((J : ℝ) + 1))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj => hNd j N N' (hNdle j hj).1 (hNdle j hj).2).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the inclusion
  have hsub : {ω | ∃ x ∈ B, eps ≤ |(PN N ω).kernelResolventReal m (h N ω) x -
      (PN N' ω).kernelResolventReal m (h N' ω) x|} ⊆
      Tt N ∪ Tt N' ∪ Cau N ∪ Cau N' ∪ Jb ∪ Z ∪ Det := by
    rintro ω ⟨x, hx, hbig⟩
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hnot
    have h6' : (∀ (L : ℕ) (x : SpatialCoordinates d) (t : ℝ≥0),
        (KN L (ω, x)).map (fun path : DiffusionPath d => path t) = PN L ω t x) ∧
        ∀ L, Continuous (h L ω) := by
      by_contra hc; exact h6 hc
    obtain ⟨hmω, hcω⟩ := h6'
    have h5' : ∃ j < J, ∀ y ∈ K', |h M ω y - φ j y| ≤ β := by
      by_contra hc; exact h5 hc
    obtain ⟨j, hjJ, hj⟩ := h5'
    have hdetx : |(PN N ω).kernelResolventReal m (φ j) x -
        (PN N' ω).kernelResolventReal m (φ j) x| < eps / 5 := by
      by_contra hc
      push_neg at hc
      exact h7 (Set.mem_biUnion (Finset.mem_range.mpr hjJ) ⟨x, hx, hc⟩)
    have hκ1 : KN N (ω, x) Aᶜ ≤ ENNReal.ofReal δ := by
      by_contra hc; push_neg at hc; exact h1 ⟨x, hx, hc⟩
    have hκ2 : KN N' (ω, x) Aᶜ ≤ ENNReal.ofReal δ := by
      by_contra hc; push_neg at hc; exact h2 ⟨x, hx, hc⟩
    have hab : ∀ y ∈ K', |h N ω y - h M ω y| ≤ β := by
      intro y hy; by_contra hc; push_neg at hc; exact h3 ⟨y, hy, hc.le⟩
    have ha'b : ∀ y ∈ K', |h N' ω y - h M ω y| ≤ β := by
      intro y hy; by_contra hc; push_neg at hc; exact h4 ⟨y, hy, hc.le⟩
    haveI := hKN N
    haveI := hKN N'
    have := aux_determining_functional_convergence_step_point (PN N ω) (PN N' ω) x
      (KN N (ω, x)) (KN N' (ω, x)) (hmω N x) (hmω N' x) hm' (h N ω) (h M ω) (φ j) (h N' ω)
      (hcω N).measurable (hcω M).measurable (φ j).continuous.measurable (hcω N').measurable
      hC hβ.le hδ.le (hbd N ω) (hbd M ω) (hφb j) (hbd N' ω) A hAm K' hAK hκ1 hκ2 hab ha'b hj
      hdetx hbudget
    linarith
  calc μ {ω | ∃ x ∈ B, eps ≤ |(PN N ω).kernelResolventReal m (h N ω) x -
        (PN N' ω).kernelResolventReal m (h N' ω) x|}
      ≤ μ (Tt N ∪ Tt N' ∪ Cau N ∪ Cau N' ∪ Jb ∪ Z ∪ Det) := measure_mono hsub
    _ ≤ μ (Tt N) + μ (Tt N') + μ (Cau N) + μ (Cau N') + μ Jb + μ Z + μ Det := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (rho / 8) + ENNReal.ofReal (rho / 8) + ENNReal.ofReal (rho / 8) +
          ENNReal.ofReal (rho / 8) + ENNReal.ofReal (rho / 8) + 0 +
          (J : ℝ≥0∞) * ENNReal.ofReal (rho / (8 * ((J : ℝ) + 1))) := by
        rw [← hρ'def]
        exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (hTt N) (hTt N')) hCauN) hCauN') hJ) hZ.le) hDet
    _ ≤ ENNReal.ofReal rho := aux_determining_functional_convergence_arith J hrho

end

section
open Topology

/-- The nested finite-cutoff resolvents `R_{N,n_i}(f_i R_{N,n_j}(f_j ⋯))` along a list of
indices, innermost datum `1`. -/
noncomputable def aux_determining_functional_convergence_nest {d k : ℕ}
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ) (n : Fin k → ℕ)
    (N : ℕ) (ω : BilateralField d) (L : List (Fin k)) : SpatialCoordinates d → ℝ :=
  L.foldr (fun i (g : SpatialCoordinates d → ℝ) => fun y =>
    (PN N ω).kernelResolventReal (n i) (fun z => f i z * g z) y) (fun _ => 1)

/-- The resolvent-contraction bound of the nested resolvents. -/
noncomputable def aux_determining_functional_convergence_bnd {d k : ℕ}
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ) (n : Fin k → ℕ)
    (L : List (Fin k)) : ℝ :=
  L.foldr (fun i c => ‖f i‖ * c / (n i : ℝ)) 1

theorem aux_determining_functional_convergence_bnd_nonneg {d k : ℕ}
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ) (n : Fin k → ℕ)
    (L : List (Fin k)) : 0 ≤ aux_determining_functional_convergence_bnd f n L := by
  induction L with
  | nil => simp [aux_determining_functional_convergence_bnd]
  | cons i L ih =>
    simp only [aux_determining_functional_convergence_bnd, List.foldr_cons] at ih ⊢
    exact div_nonneg (mul_nonneg (norm_nonneg _) ih) (Nat.cast_nonneg _)

theorem aux_determining_functional_convergence_foldr_get {k : ℕ} {β : Type*}
    (F : Fin k → β → β) (b : β) (L : List (Fin k)) :
    (List.finRange L.length).foldr (fun j => F (L.get j)) b = L.foldr F b := by
  have h := congrArg (fun l : List (Fin k) => l.foldr F b) (List.map_get_finRange L)
  simp only [List.foldr_map] at h
  exact h

/-- Measurable versions of the nested resolvents, through the path-functional identity. -/
theorem aux_determining_functional_convergence_version
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN) {k : ℕ}
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ) (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (L : List (Fin k)) (N : ℕ) :
    ∃ w : BilateralField d → SpatialCoordinates d → ℝ, (∀ y, Measurable fun ω => w ω y) ∧
      ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure,
        aux_determining_functional_convergence_nest PN f n N ω L = w ω := by
  have hid := determining_functional_identity M H PN KN hKN hin
    (fun N ω m g x => (PN N ω).kernelResolventReal (m : ℝ) g x) (fun _ _ _ _ _ => rfl)
    L.length (fun j => f (L.get j)) (fun j => n (L.get j)) (fun j => hn _)
    (fun path => ∫ s in Set.pi Set.univ (fun _ : Fin L.length => Set.Ioi (0 : ℝ)),
      Real.exp (-(∑ i : Fin L.length, (n (L.get i) : ℝ) * s i)) *
        ∏ i : Fin L.length, f (L.get i) (path (Real.toNNReal
          (∑ j ∈ Finset.univ.filter (fun j : Fin L.length => j ≤ i), s j)))) (fun _ => rfl)
  rcases hid with ⟨hPc, -, hid3, -⟩
  refine ⟨fun ω y => ∫ path, (fun path : DiffusionPath d =>
      ∫ s in Set.pi Set.univ (fun _ : Fin L.length => Set.Ioi (0 : ℝ)),
      Real.exp (-(∑ i : Fin L.length, (n (L.get i) : ℝ) * s i)) *
        ∏ i : Fin L.length, f (L.get i) (path (Real.toNNReal
          (∑ j ∈ Finset.univ.filter (fun j : Fin L.length => j ≤ i), s j)))) path
      ∂(KN N (ω, y)), fun y => ?_, ?_⟩
  · exact (hPc.measurable.stronglyMeasurable.integral_kernel (κ := KN N)).measurable.comp
      (measurable_id.prodMk measurable_const)
  · filter_upwards [hid3] with ω hω
    funext y
    rw [hω N y]
    have e := aux_determining_functional_convergence_foldr_get
      (fun i (g : SpatialCoordinates d → ℝ) =>
        fun y => (PN N ω).kernelResolventReal (n i) (fun z => f i z * g z) y)
      (fun _ => (1 : ℝ)) L
    exact (congrFun e y).symm

end

section
open Topology

/-- **Finite recursion from the innermost resolvent outward.**  Every nested resolvent is
bounded by the product of the resolvent contractions, continuous on the environments where
the finite-cutoff resolvents of bounded continuous data are continuous, and Cauchy locally
uniformly in probability. -/
theorem aux_determining_functional_convergence_nested
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d)) [IsProbabilityMeasure μ]
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hmarg : ∀ᵐ ω ∂μ, ∀ (N : ℕ) (x : SpatialCoordinates d) (t : ℝ≥0),
      (KN N (ω, x)).map (fun path : DiffusionPath d => path t) = PN N ω t x)
    (hdet : ∀ m : ℕ, 0 < m → ∀ φ : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
        μ {ω | ∃ x ∈ B, eps ≤ |(PN N ω).kernelResolventReal m φ x -
          (PN N' ω).kernelResolventReal m φ x|} ≤ ENNReal.ofReal rho)
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∃ A : Set (DiffusionPath d), IsCompact A ∧ ∀ N : ℕ,
        (∫⁻ ω, ⨆ x ∈ B, KN N (ω, x) Aᶜ ∂μ) ≤ ENNReal.ofReal eps)
    {k : ℕ} (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (Gc : Set (BilateralField d)) (hGc : ∀ᵐ ω ∂μ, ω ∈ Gc)
    (hcontG : ∀ ω ∈ Gc, ∀ (N m : ℕ), 0 < m →
      ∀ φ : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Continuous ((PN N ω).kernelResolventReal m φ))
    (hver : ∀ (L : List (Fin k)) (N : ℕ), ∃ w : BilateralField d → SpatialCoordinates d → ℝ,
      (∀ y, Measurable fun ω => w ω y) ∧
        ∀ᵐ ω ∂μ, aux_determining_functional_convergence_nest PN f n N ω L = w ω) :
    ∀ L : List (Fin k),
      (∀ N ω y, |aux_determining_functional_convergence_nest PN f n N ω L y| ≤
        aux_determining_functional_convergence_bnd f n L) ∧
      (∀ ω ∈ Gc, ∀ N, Continuous (aux_determining_functional_convergence_nest PN f n N ω L)) ∧
      (∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
        ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
          μ {ω | ∃ x ∈ B, eps ≤ |aux_determining_functional_convergence_nest PN f n N ω L x -
            aux_determining_functional_convergence_nest PN f n N' ω L x|} ≤
            ENNReal.ofReal rho) := by
  intro L
  induction L with
  | nil =>
    refine ⟨fun N ω y => by simp [aux_determining_functional_convergence_nest,
      aux_determining_functional_convergence_bnd], fun ω _ N => continuous_const,
      fun B _ eps heps rho _ => ⟨0, fun N N' _ _ => ?_⟩⟩
    have hempty : {ω | ∃ x ∈ B, eps ≤ |aux_determining_functional_convergence_nest PN f n N ω []
        x - aux_determining_functional_convergence_nest PN f n N' ω [] x|} = ∅ := by
      ext ω
      simp only [aux_determining_functional_convergence_nest, List.foldr_nil, sub_self,
        abs_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_le]
      intro _ _; exact heps
    rw [hempty, measure_empty]
    exact zero_le
  | cons i L ih =>
    obtain ⟨ihb, ihc, ihcau⟩ := ih
    have hbL := aux_determining_functional_convergence_bnd_nonneg f n L
    have hni : (0 : ℝ) < n i := Nat.cast_pos.mpr (hn i)
    let hf : ℕ → BilateralField d → SpatialCoordinates d → ℝ := fun N ω z =>
      f i z * aux_determining_functional_convergence_nest PN f n N ω L z
    have hbd : ∀ N ω z, |hf N ω z| ≤ ‖f i‖ * aux_determining_functional_convergence_bnd f n L := by
      intro N ω z
      simp only [hf, abs_mul]
      exact mul_le_mul ((f i).norm_coe_le_norm z) (ihb N ω z) (abs_nonneg _) (norm_nonneg _)
    have hC : 0 ≤ ‖f i‖ * aux_determining_functional_convergence_bnd f n L :=
      mul_nonneg (norm_nonneg _) hbL
    refine ⟨fun N ω y => ?_, fun ω hω N => ?_, ?_⟩
    · change |(PN N ω).kernelResolventReal (n i) (hf N ω) y| ≤
        ‖f i‖ * aux_determining_functional_convergence_bnd f n L / (n i : ℝ)
      exact (PN N ω).norm_kernelResolventReal_le hni (hbd N ω) y
    · have hcf : Continuous (hf N ω) := (f i).continuous.mul (ihc ω hω N)
      let F : BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
        BoundedContinuousFunction.mkOfBound ⟨hf N ω, hcf⟩
          (2 * (‖f i‖ * aux_determining_functional_convergence_bnd f n L)) (fun y z => by
            rw [Real.dist_eq]
            have h1 := abs_le.mp (hbd N ω y)
            have h2 := abs_le.mp (hbd N ω z)
            exact abs_le.mpr ⟨by simp only [ContinuousMap.coe_mk]; linarith,
              by simp only [ContinuousMap.coe_mk]; linarith⟩)
      exact hcontG ω hω N (n i) (hn i) F
    · refine aux_determining_functional_convergence_step μ PN KN hKN hmarg hdet htight (n i)
        (hn i) hf _ hC hbd ?_ ?_ ?_
      · filter_upwards [hGc] with ω hω N
        exact (f i).continuous.mul (ihc ω hω N)
      · intro N
        obtain ⟨w, hwm, hw⟩ := hver L N
        refine ⟨fun ω z => f i z * w ω z, fun y => (hwm y).const_mul _, ?_⟩
        filter_upwards [hw] with ω hω
        funext z
        simp only [hf, hω]
      · intro B hB eps heps rho hrho
        have hfe : 0 < eps / (‖f i‖ + 1) := div_pos heps (by positivity)
        obtain ⟨N0, hN0⟩ := ihcau B hB _ hfe rho hrho
        refine ⟨N0, fun N N' hN hN' => (measure_mono ?_).trans (hN0 N N' hN hN')⟩
        rintro ω ⟨x, hx, hbig⟩
        refine ⟨x, hx, ?_⟩
        by_contra hlt
        push_neg at hlt
        have hkey : |hf N ω x - hf N' ω x| < eps := by
          simp only [hf]
          rw [← mul_sub, abs_mul]
          have h1 : |f i x| * |aux_determining_functional_convergence_nest PN f n N ω L x -
              aux_determining_functional_convergence_nest PN f n N' ω L x| ≤
              ‖f i‖ * (eps / (‖f i‖ + 1)) :=
            mul_le_mul ((f i).norm_coe_le_norm x) hlt.le (abs_nonneg _) (norm_nonneg _)
          have h2 : ‖f i‖ * (eps / (‖f i‖ + 1)) < eps := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg (f i)]
          linarith
        linarith

end



theorem determining_functional_convergence
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (RN : Nat → BilateralField d → Nat →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega n f x, RN N omega n f x =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) *
        kernelIntegral (PN N omega (Real.toNNReal t)) f x)
    (hcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N n, 0 < n → ∀ f, Continuous (RN N omega n f))
    (hdet : ∀ n : Nat, 0 < n →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : Nat, ∀ N N' : Nat, N0 ≤ N → N0 ≤ N' →
        (chaosSampleLaw M).toMeasure
          {omega | ∃ x ∈ B, eps ≤ |RN N omega n f x - RN N' omega n f x|} ≤
            ENNReal.ofReal rho)
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∃ A : Set (DiffusionPath d), IsCompact A ∧
        ∀ N : Nat,
          (∫⁻ omega, ⨆ x : B, KN N (omega, x.val) Aᶜ ∂(chaosSampleLaw M).toMeasure) ≤
            ENNReal.ofReal eps)
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
    ∃ U : BilateralField d → C(SpatialCoordinates d, ℝ), Measurable U ∧
      (∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
          (chaosSampleLaw M).toMeasure
            {omega | ∃ x ∈ B,
              eps ≤ |(∫ path, Psi path ∂(KN N (omega, x))) - U omega x|} ≤
                ENNReal.ofReal rho) := by
  have hRN' : ∀ N omega n (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) x,
      RN N omega n f x = (PN N omega).kernelResolventReal (n : ℝ) f x := hRN
  have hmarg : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (x : SpatialCoordinates d)
      (t : ℝ≥0), (KN N (omega, x)).map (fun path : DiffusionPath d => path t) =
        PN N omega t x := by
    filter_upwards [hin.2.2] with omega hω
    intro N x t
    refine aux_determining_functional_convergence_marginal (PN N omega) x (KN N (omega, x))
      (fun I => ?_) t
    have heval : Measurable (ContinuousPath.finsetEvaluation
        (alpha := SpatialCoordinates d) I) := by
      rw [measurable_pi_iff]
      intro s
      exact ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d)
        (s : NNReal)
    have h := hω N I x
    rw [Kernel.map_apply _ heval] at h
    exact h
  have hdet' : ∀ m : ℕ, 0 < m → ∀ φ : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
        (chaosSampleLaw M).toMeasure {omega | ∃ x ∈ B, eps ≤
          |(PN N omega).kernelResolventReal m φ x -
            (PN N' omega).kernelResolventReal m φ x|} ≤ ENNReal.ofReal rho := by
    intro m hm φ B hB eps heps rho hrho
    have h := hdet m hm φ B hB eps heps rho hrho
    obtain ⟨N0, hN0⟩ := h
    refine ⟨N0, fun N N' h1 h2 => ?_⟩
    have h3 := hN0 N N' h1 h2
    simp only [hRN'] at h3
    exact h3
  have htight' : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∃ A : Set (DiffusionPath d), IsCompact A ∧ ∀ N : ℕ,
        (∫⁻ omega, ⨆ x ∈ B, KN N (omega, x) Aᶜ ∂(chaosSampleLaw M).toMeasure) ≤
          ENNReal.ofReal eps := by
    intro B hB eps heps
    have h := htight B hB eps heps
    obtain ⟨A, hA, hAN⟩ := h
    refine ⟨A, hA, fun N => ?_⟩
    have h1 := hAN N
    simp only [iSup_subtype] at h1
    exact h1
  let Gc : Set (BilateralField d) := {omega | ∀ (N m : ℕ), 0 < m →
    ∀ φ : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      Continuous ((PN N omega).kernelResolventReal m φ)}
  have hGc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, omega ∈ Gc := by
    filter_upwards [hcont] with omega hω
    intro N m hm φ
    have h := hω N m hm φ
    have he : RN N omega m φ = (PN N omega).kernelResolventReal m φ :=
      funext fun x => hRN' N omega m φ x
    rw [he] at h
    exact h
  have hver := fun L N => aux_determining_functional_convergence_version M H PN KN hKN hin
    f n hn L N
  have hnest := aux_determining_functional_convergence_nested (chaosSampleLaw M).toMeasure
    PN KN hKN hmarg hdet' htight' f n hn Gc hGc (fun omega hω => hω) hver (List.finRange k)
  obtain ⟨-, hVc, hVcau⟩ := hnest
  have hid := determining_functional_identity M H PN KN hKN hin
    (fun N omega m g x => (PN N omega).kernelResolventReal (m : ℝ) g x)
    (fun _ _ _ _ _ => rfl) k f n hn Psi hPsi
  obtain ⟨hPc, -, hid3, -⟩ := hid
  have hu_eq : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      (fun x => ∫ path, Psi path ∂(KN N (omega, x))) =
        aux_determining_functional_convergence_nest PN f n N omega (List.finRange k) := by
    filter_upwards [hid3] with omega hω N
    funext x
    exact hω N x
  have hmeas : ∀ (N : ℕ) (x : SpatialCoordinates d),
      Measurable fun omega => ∫ path, Psi path ∂(KN N (omega, x)) := fun N x =>
    (hPc.measurable.stronglyMeasurable.integral_kernel (κ := KN N)).measurable.comp
      (measurable_id.prodMk measurable_const)
  have hucont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      Continuous (fun x => ∫ path, Psi path ∂(KN N (omega, x))) := by
    filter_upwards [hu_eq, hGc] with omega h1 h2 N
    rw [h1 N]
    exact hVc omega h2 N
  have hucau : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N P : ℕ, N0 ≤ N → N0 ≤ P →
        (chaosSampleLaw M).toMeasure {omega | ∃ x ∈ B,
          eps ≤ |(∫ path, Psi path ∂(KN N (omega, x))) -
            ∫ path, Psi path ∂(KN P (omega, x))|} ≤ ENNReal.ofReal rho := by
    intro B hB eps heps rho hrho
    obtain ⟨N0, hN0⟩ := hVcau B hB eps heps rho hrho
    refine ⟨N0, fun N P hN hP => ?_⟩
    have hZ := ae_iff.mp hu_eq
    refine (measure_mono (t := {omega | ∃ x ∈ B,
        eps ≤ |aux_determining_functional_convergence_nest PN f n N omega (List.finRange k) x -
          aux_determining_functional_convergence_nest PN f n P omega (List.finRange k) x|} ∪
        {omega | ¬ ∀ N, (fun x => ∫ path, Psi path ∂(KN N (omega, x))) =
          aux_determining_functional_convergence_nest PN f n N omega (List.finRange k)})
        ?_).trans ((measure_union_le _ _).trans ?_)
    · rintro omega ⟨x, hx, hbig⟩
      by_cases hω : ∀ N, (fun x => ∫ path, Psi path ∂(KN N (omega, x))) =
          aux_determining_functional_convergence_nest PN f n N omega (List.finRange k)
      · left
        refine ⟨x, hx, ?_⟩
        rw [← hω N, ← hω P]
        exact hbig
      · right
        exact hω
    · rw [hZ, add_zero]
      exact hN0 N P hN hP
  have hcomp := Paper.aux_tight_whole_space_resolvent_limit_completion (chaosSampleLaw M).toMeasure
    (fun N omega x => ∫ path, Psi path ∂(KN N (omega, x))) hmeas hucont hucau
  obtain ⟨U, -, -, hUm, -, hconv⟩ := hcomp
  exact ⟨U, hUm, hconv⟩

end Paper
