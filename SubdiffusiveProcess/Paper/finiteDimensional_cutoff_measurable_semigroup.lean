module

public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.resolvent_datum
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_nonexplosion

public import MarkovProcess.Parameterized.Semigroup
public import MarkovProcess.Examples.Identity
public import MarkovProcess.Semigroup.Generation
public import MarkovProcess.Semigroup.PositiveShift
public import MarkovProcess.Kernel.MeasurableRadonFamily
public import MarkovProcess.Kernel.C0SemigroupJoint
public import MarkovProcess.Feller.Resolvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumUniqueness
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Group.ZeroAtInfty
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.MetricSpace.Polish
public import SubdiffusiveProcess.Meta.NormedAlgebraRatCache

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Patch a jointly measurable family by the identity semigroup outside a measurable event. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity
    {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (G : Set Theta) (hG : MeasurableSet G) :
    ParameterizedSubMarkovKernelSemigroup Theta alpha := by
  classical
  letI : DecidablePred (fun theta : Theta => theta ∈ G) := Classical.decPred _
  letI : DecidablePred (fun q : Theta × (NNReal × alpha) => q.1 ∈ G) := Classical.decPred _
  exact {
  kernel theta t := if theta ∈ G then P theta t else Kernel.id
  measurable_kernel := by
    classical
    let s : Set (Theta × (NNReal × alpha)) := {q | q.1 ∈ G}
    have hcond : MeasurableSet s := hG.preimage measurable_fst
    have hP : Measurable (fun q : Theta × (NNReal × alpha) => P q.1 q.2.1 q.2.2) :=
      P.measurable_kernel
    have hId : Measurable (fun q : Theta × (NNReal × alpha) =>
        (Kernel.id : Kernel alpha alpha) q.2.2) :=
      (Kernel.id : Kernel alpha alpha).measurable.comp measurable_snd.snd
    let : DecidablePred (· ∈ s) := Classical.decPred _
    have hpiece := @Measurable.piecewise _ _ s _ _ _ _
      (Classical.decPred _) hcond hP hId
    have heq :
        (s.piecewise
          (fun q : Theta × (NNReal × alpha) => P q.1 q.2.1 q.2.2)
          (fun q => (Kernel.id : Kernel alpha alpha) q.2.2)) =
        (fun q : Theta × (NNReal × alpha) =>
          (if q.1 ∈ G then P q.1 q.2.1 else Kernel.id) q.2.2) := by
      funext q
      by_cases h : q.1 ∈ G <;> simp [h, Set.piecewise, s]
    rw [← heq]
    exact hpiece
  kernel_zero theta := by
    by_cases h : theta ∈ G <;> simp [h, P.kernel_zero theta]
  kernel_add theta s t := by
    by_cases h : theta ∈ G
    · simp [h, P.kernel_add theta s t]
    · simp [h]
  isSubMarkovKernel theta t := by
    by_cases h : theta ∈ G
    · simpa [h] using P.isSubMarkovKernel theta t
    · simpa [h] using (IsSubMarkovKernel.id : IsSubMarkovKernel (Kernel.id : Kernel alpha alpha))
  }

theorem aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity_inside
    {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (G : Set Theta) (hG : MeasurableSet G)
    (theta : Theta) (htheta : theta ∈ G) :
    (aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity P G hG).toSubMarkovKernelSemigroup theta =
      P.toSubMarkovKernelSemigroup theta := by
  apply SubMarkovKernelSemigroup.ext
  intro t
  simp [aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity, htheta]

theorem aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity_conservative
    {Theta alpha : Type*} [MeasurableSpace Theta]
    [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (G : Set Theta) (hG : MeasurableSet G)
    (hP : ∀ theta ∈ G, (P.toSubMarkovKernelSemigroup theta).IsConservative) :
    ∀ theta, ((aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity P G hG).toSubMarkovKernelSemigroup theta).IsConservative := by
  intro theta
  by_cases h : theta ∈ G
  · rw [aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity_inside P G hG theta h]
    exact hP theta h
  · have heq :
      (aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity P G hG).toSubMarkovKernelSemigroup theta =
        (MarkovProcess.idSemigroup (alpha := alpha)) := by
      apply SubMarkovKernelSemigroup.ext
      intro t
      simp [aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity, MarkovProcess.idSemigroup, h]
    rw [heq]
    exact MarkovProcess.isConservative_idSemigroup

theorem aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity_feller
    {Theta alpha : Type*} [MeasurableSpace Theta]
    [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] [LocallyCompactSpace alpha]
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (G : Set Theta) (hG : MeasurableSet G)
    (hP : ∀ theta ∈ G, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup) :
    ∀ theta, ((aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity P G hG).toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup := by
  intro theta
  by_cases h : theta ∈ G
  · rw [aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity_inside P G hG theta h]
    exact hP theta h
  · have heq :
      (aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity P G hG).toSubMarkovKernelSemigroup theta =
        (MarkovProcess.idSemigroup (alpha := alpha)) := by
      apply SubMarkovKernelSemigroup.ext
      intro t
      simp [aux_finiteDimensional_cutoff_measurable_semigroup_patchIdentity, MarkovProcess.idSemigroup, h]
    rw [heq]
    exact MarkovProcess.isFellerKernelSemigroup_idSemigroup

/-! ### Proof route

The given family `PN` is itself jointly measurable on a measurable full event `G`, and is
patched by the identity semigroup off `G`.  On `G` the `C₀` resolvent of `PN N ω` equals the
weak elliptic resolvent datum of `hres`, i.e. the unique `C₀` function solving
`μ ρ u − ∇·(c ∇u) = ρ f` weakly on every centred cube for the actual cutoff pair
`(c, ρ) = (a_N⁻¹ e^{h_N − z}, e^{h_N − z})` (whole-space uniqueness,
`eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact`).

* `aux_graph`: over potentials `p ∈ C(ℝᵈ, ℝ)` the solution graph is analytic (a countable
  intersection of projections of closed sets in `C(ℝᵈ) × C₀ × L²(cube)ᵈ`) and single-valued, so
  Lusin separation makes the solution map Borel on its domain; composing with the measurable
  potential `ω ↦ h_N^ω` gives measurability of every resolvent orbit on `G`.
* `aux_hilleYosida`: the generated semigroup is the strong limit of Yosida exponentials, so it
  is measurable in the parameter whenever the resolvents are.
* `aux_orbits`, `aux_patch`: Carathéodory joint measurability in `(t, x)` and the Riesz
  `C_c`-test criterion give the jointly measurable kernel.

No measurability of `PN`, nonexplosion bound or regularity of the potential is used beyond
continuity; `hnonexplosion` and `hd` are not needed. -/

section aux_hilleYosida

open Filter MeasureTheory Topology
open scoped NNReal

open MarkovProcess MarkovProcess.Semigroup

/-- Joint measurability of a measurable family of continuous linear maps, evaluated along a
measurable vector field. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_measurable_clm_comp
    {Θ E : Type*} [MeasurableSpace Θ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (A : Θ → E →L[ℝ] E) (hA : ∀ y, Measurable fun θ ↦ A θ y)
    {g : Θ → E} (hg : Measurable g) :
    Measurable fun θ ↦ A θ (g θ) := by
  have hjoint : Measurable (Function.uncurry fun (y : E) (θ : Θ) ↦ A θ y) :=
    measurable_uncurry_of_continuous_of_measurable (fun θ ↦ (A θ).continuous) hA
  exact hjoint.comp (hg.prodMk measurable_id)

/-- Iterates of a measurable family of continuous linear maps are measurable. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_measurable_clm_iterate
    {Θ E : Type*} [MeasurableSpace Θ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (A : Θ → E →L[ℝ] E) (hA : ∀ y, Measurable fun θ ↦ A θ y) (n : ℕ) (y : E) :
    Measurable fun θ ↦ (A θ)^[n] y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact aux_finiteDimensional_cutoff_measurable_semigroup_measurable_clm_comp A hA ih

/-- The exponential of a measurable family of continuous linear maps acts measurably. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_measurable_exp
    {Θ E : Type*} [MeasurableSpace Θ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (A : Θ → E →L[ℝ] E) (hA : ∀ y, Measurable fun θ ↦ A θ y) (y : E) :
    Measurable fun θ ↦ NormedSpace.exp (A θ) y := by
  have hsum : ∀ θ, HasSum (fun n : ℕ ↦ ((n.factorial : ℝ)⁻¹) • (A θ)^[n] y)
      (NormedSpace.exp (A θ) y) := by
    intro θ
    have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (A θ)).mapL
      (ContinuousLinearMap.apply ℝ E y)
    simpa [ContinuousLinearMap.toLinearMap_pow] using h
  refine measurable_of_tendsto_metrizable (f := fun N θ ↦
      ∑ n ∈ Finset.range N, ((n.factorial : ℝ)⁻¹) • (A θ)^[n] y) ?_ ?_
  · intro N
    refine Finset.measurable_sum _ fun n _ ↦ ?_
    exact (aux_finiteDimensional_cutoff_measurable_semigroup_measurable_clm_iterate
      A hA n y).const_smul _
  · exact tendsto_pi_nhds.2 fun θ ↦ (hsum θ).tendsto_sum_nat

/-- **Parametric Hille--Yosida measurability.** If every resolvent operator of a family of
contractive resolvents is measurable in the parameter, so is every orbit of the generated
semigroup. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_measurable_generated
    {Θ E : Type*} [MeasurableSpace Θ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (R : Θ → ContractiveResolvent E)
    (hR : ∀ α y, Measurable fun θ ↦ (R θ).operator α y) (t : NNReal) (y : E) :
    Measurable fun θ ↦ (R θ).generatedSemigroup t y := by
  have hgen : ∀ α (z : E), Measurable fun θ ↦ ((t : ℝ) • (R θ).yosidaGenerator α) z := by
    intro α z
    have h1 : Measurable fun θ ↦ (R θ).operator α z := hR α z
    have h2 : Measurable fun θ ↦
        (t : ℝ) • ((α : ℝ) • ((α : ℝ) • (R θ).operator α z - z)) :=
      ((h1.const_smul _).sub measurable_const |>.const_smul _).const_smul _
    convert h2 using 2 with θ
    simp [ContractiveResolvent.yosidaGenerator, ContractiveResolvent.scaledOperator]
  have hyos : ∀ n : ℕ, Measurable fun θ ↦
      (R θ).yosidaOperator (naturalShift n) t y := by
    intro n
    exact aux_finiteDimensional_cutoff_measurable_semigroup_measurable_exp
      (fun θ ↦ (t : ℝ) • (R θ).yosidaGenerator (naturalShift n))
      (hgen _) y
  refine measurable_of_tendsto_metrizable hyos ?_
  exact tendsto_pi_nhds.2 fun θ ↦
    (R θ).tendsto_yosidaOperator_naturalShift_apply t y

end aux_hilleYosida

section aux_c0Separable

open Filter Topology Metric
open scoped ZeroAtInfty

/-- The radial cutoff equal to one on `closedBall 0 n` and vanishing off `ball 0 (n + 1)`. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_cutoff (d n : ℕ) :
    C(Fin d → ℝ, ℝ) :=
  ⟨fun x ↦ max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)), by fun_prop⟩

theorem aux_finiteDimensional_cutoff_measurable_semigroup_cutoff_apply (d n : ℕ)
    (x : Fin d → ℝ) :
    aux_finiteDimensional_cutoff_measurable_semigroup_cutoff d n x =
      max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)) := rfl

/-- A continuous function cut off radially, as an element of `C₀`. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_cutoffMul (d n : ℕ)
    (q : C(Fin d → ℝ, ℝ)) : C₀(Fin d → ℝ, ℝ) where
  toFun x := aux_finiteDimensional_cutoff_measurable_semigroup_cutoff d n x * q x
  continuous_toFun := by fun_prop
  zero_at_infty' := by
    have hcs : HasCompactSupport (fun x ↦
        aux_finiteDimensional_cutoff_measurable_semigroup_cutoff d n x * q x) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℝ) ((n : ℝ) + 1)) ?_
      intro x hx
      have hx' : (n : ℝ) + 1 < ‖x‖ := by
        simpa [mem_closedBall, dist_zero_right, not_le] using hx
      have hzero : aux_finiteDimensional_cutoff_measurable_semigroup_cutoff d n x = 0 := by
        rw [aux_finiteDimensional_cutoff_measurable_semigroup_cutoff_apply]
        have h1 : min 1 ((n : ℝ) + 1 - ‖x‖) ≤ 0 := (min_le_right _ _).trans (by linarith)
        exact max_eq_left h1
      simp [hzero]
    exact hcs.is_zero_at_infty

theorem aux_finiteDimensional_cutoff_measurable_semigroup_cutoffMul_apply (d n : ℕ)
    (q : C(Fin d → ℝ, ℝ)) (x : Fin d → ℝ) :
    aux_finiteDimensional_cutoff_measurable_semigroup_cutoffMul d n q x =
      aux_finiteDimensional_cutoff_measurable_semigroup_cutoff d n x * q x := rfl

/-- Functions vanishing at infinity on `ℝᵈ` form a separable space. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_c0_separable (d : ℕ) :
    TopologicalSpace.SeparableSpace C₀(Fin d → ℝ, ℝ) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense C(Fin d → ℝ, ℝ)
  let S : Set C₀(Fin d → ℝ, ℝ) :=
    ⋃ n : ℕ, (aux_finiteDimensional_cutoff_measurable_semigroup_cutoffMul d n) '' D
  have hSc : S.Countable := Set.countable_iUnion fun n ↦ hDc.image _
  refine ⟨⟨S, hSc, ?_⟩⟩
  rw [Metric.dense_iff]
  intro f ε hε
  -- decay of `f` outside a ball
  have hdecay : ∃ n : ℕ, ∀ x : Fin d → ℝ, (n : ℝ) ≤ ‖x‖ → |f x| < ε / 2 := by
    have ht := zero_at_infty f
    have hmem : {x : Fin d → ℝ | |f x| < ε / 2} ∈ cocompact (Fin d → ℝ) := by
      have hb : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 (0 : ℝ) := ball_mem_nhds _ (by linarith)
      have hpre : f ⁻¹' Metric.ball (0 : ℝ) (ε / 2) ∈ cocompact (Fin d → ℝ) := ht hb
      have heq : f ⁻¹' Metric.ball (0 : ℝ) (ε / 2) = {x | |f x| < ε / 2} := by
        ext x
        simp [Metric.mem_ball]
      rwa [heq] at hpre
    obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 hmem
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Fin d → ℝ)
    obtain ⟨n, hn⟩ := exists_nat_gt R
    refine ⟨n, fun x hx ↦ ?_⟩
    have hxK : x ∉ K := by
      intro hxK
      have := hR hxK
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    exact hKs hxK
  obtain ⟨n, hn⟩ := hdecay
  -- approximation on the compact ball
  have happrox : ∃ q ∈ D, ∀ x ∈ closedBall (0 : Fin d → ℝ) ((n : ℝ) + 1),
      |f x - q x| < ε / 2 := by
    have hf : (f : C(Fin d → ℝ, ℝ)) ∈ closure D := hDd.closure_eq ▸ Set.mem_univ _
    obtain ⟨q, hqD, hq⟩ := mem_closure_iff_seq_limit.1 hf
    have hunif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hq)
      _ (isCompact_closedBall (0 : Fin d → ℝ) ((n : ℝ) + 1))
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    obtain ⟨j, hj⟩ := (hunif (ε / 2) (by linarith)).exists
    refine ⟨q j, hqD j, fun x hx ↦ ?_⟩
    have := hj x hx
    simpa [Real.dist_eq] using this
  obtain ⟨q, hqD, hq⟩ := happrox
  refine ⟨aux_finiteDimensional_cutoff_measurable_semigroup_cutoffMul d n q, ?_,
    Set.mem_iUnion.2 ⟨n, Set.mem_image_of_mem _ hqD⟩⟩
  rw [Metric.mem_ball, dist_comm]
  rw [dist_eq_norm, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine (BoundedContinuousFunction.norm_le (by linarith)).2 fun x ↦ ?_
  change ‖f x - aux_finiteDimensional_cutoff_measurable_semigroup_cutoffMul d n q x‖ ≤ ε / 2
  rw [aux_finiteDimensional_cutoff_measurable_semigroup_cutoffMul_apply,
    aux_finiteDimensional_cutoff_measurable_semigroup_cutoff_apply, Real.norm_eq_abs]
  set c : ℝ := max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)) with hc
  have hc0 : 0 ≤ c := le_max_left _ _
  have hc1 : c ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have hsplit : f x - c * q x = (1 - c) * f x + c * (f x - q x) := by ring
  have hA : (1 - c) * |f x| ≤ (1 - c) * (ε / 2) := by
    rcases lt_or_ge ‖x‖ (n : ℝ) with hx | hx
    · have : c = 1 := by
        rw [hc]
        have : min 1 ((n : ℝ) + 1 - ‖x‖) = 1 := min_eq_left (by linarith)
        rw [this]; exact max_eq_right zero_le_one
      simp [this]
    · exact mul_le_mul_of_nonneg_left (hn x hx).le (by linarith)
  have hB : c * |f x - q x| ≤ c * (ε / 2) := by
    rcases le_or_gt ‖x‖ ((n : ℝ) + 1) with hx | hx
    · have hmem : x ∈ closedBall (0 : Fin d → ℝ) ((n : ℝ) + 1) := by
        simpa [mem_closedBall, dist_zero_right] using hx
      exact mul_le_mul_of_nonneg_left (hq x hmem).le hc0
    · have : c = 0 := by
        rw [hc]
        exact max_eq_left ((min_le_right _ _).trans (by linarith))
      simp [this]
  calc |f x - c * q x| = |(1 - c) * f x + c * (f x - q x)| := by rw [hsplit]
    _ ≤ |(1 - c) * f x| + |c * (f x - q x)| := abs_add_le _ _
    _ = (1 - c) * |f x| + c * |f x - q x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - c), abs_of_nonneg hc0]
    _ ≤ (1 - c) * (ε / 2) + c * (ε / 2) := add_le_add hA hB
    _ = ε / 2 := by ring

theorem aux_finiteDimensional_cutoff_measurable_semigroup_c0_secondCountable (d : ℕ) :
    SecondCountableTopology C₀(Fin d → ℝ, ℝ) := by
  have := aux_finiteDimensional_cutoff_measurable_semigroup_c0_separable d
  exact UniformSpace.secondCountable_of_separable _

theorem aux_finiteDimensional_cutoff_measurable_semigroup_c0_polish (d : ℕ) :
    PolishSpace C₀(Fin d → ℝ, ℝ) := by
  have := aux_finiteDimensional_cutoff_measurable_semigroup_c0_separable d
  infer_instance

end aux_c0Separable

section aux_souslin

open Filter MeasureTheory Topology Set

/-- **Measurability from a uniquely solvable analytic relation.** Let `A ⊆ P × Y` be analytic
in a Polish product and single-valued over every parameter. If a map `s` is a section of `A`
over a measurable parameter map on a set `G`, then `s` is measurable on `G`: the two
projections of `A` over an open set and over its complement are disjoint analytic sets, and a
Lusin separating Borel set describes the preimage. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_measurable_of_analytic
    {Ω P Y : Type*} [MeasurableSpace Ω]
    [TopologicalSpace P] [T2Space P] [MeasurableSpace P] [OpensMeasurableSpace P]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    [PolishSpace (P × Y)]
    (A : Set (P × Y)) (hA : AnalyticSet A)
    (huniq : ∀ p g g', (p, g) ∈ A → (p, g') ∈ A → g = g')
    (Pot : Ω → P) (hPot : Measurable Pot) (G : Set Ω) (s : Ω → Y)
    (hs : ∀ ω ∈ G, (Pot ω, s ω) ∈ A) :
    Measurable fun ω : G ↦ s ω := by
  refine measurable_of_isOpen fun U hU ↦ ?_
  let B1 : Set P := Prod.fst '' (A ∩ (univ ×ˢ U))
  let B2 : Set P := Prod.fst '' (A ∩ (univ ×ˢ Uᶜ))
  have hU1 : AnalyticSet (univ ×ˢ U : Set (P × Y)) := by
    have := (isOpen_univ.prod hU : IsOpen (univ ×ˢ U : Set (P × Y))).analyticSet_image
      (f := (id : P × Y → P × Y)) continuous_id
    simpa using! this
  have hU2 : AnalyticSet (univ ×ˢ Uᶜ : Set (P × Y)) :=
    (isClosed_univ.prod hU.isClosed_compl).analyticSet
  have hinter : ∀ V : Set (P × Y), AnalyticSet V → AnalyticSet (A ∩ V) := by
    intro V hV
    have h := AnalyticSet.iInter (ι := Bool) (s := fun b ↦ bif b then A else V)
      (fun b ↦ by cases b <;> simpa)
    have heq : (⋂ b : Bool, bif b then A else V) = A ∩ V := by
      ext q
      simp [Bool.forall_bool, and_comm]
    rwa [heq] at h
  have hB1 : AnalyticSet B1 := (hinter _ hU1).image_of_continuous continuous_fst
  have hB2 : AnalyticSet B2 := (hinter _ hU2).image_of_continuous continuous_fst
  have hdisj : Disjoint B1 B2 := by
    rw [Set.disjoint_left]
    rintro p ⟨⟨p1, g⟩, ⟨hgA, -, hgU⟩, rfl⟩ ⟨⟨p2, g'⟩, ⟨hg'A, -, hg'U⟩, hp⟩
    simp only at hp
    subst hp
    exact hg'U (huniq _ _ _ hgA hg'A ▸ hgU)
  obtain ⟨V, hB1V, hB2V, hVm⟩ := hB1.measurablySeparable hB2 hdisj
  have hpre : (fun ω : G ↦ s ω) ⁻¹' U = (fun ω : G ↦ Pot ω) ⁻¹' V := by
    ext ω
    simp only [mem_preimage]
    constructor
    · intro hω
      exact hB1V ⟨(Pot ω, s ω), ⟨hs ω ω.2, mem_univ _, hω⟩, rfl⟩
    · intro hω
      by_contra hω'
      exact Set.disjoint_left.1 hB2V ⟨(Pot ω, s ω), ⟨hs ω ω.2, mem_univ _, hω'⟩, rfl⟩ hω
  rw [hpre]
  exact (hPot.comp measurable_subtype_coe) hVm

end aux_souslin

section aux_continuity

open Filter MeasureTheory Topology Set
open scoped ZeroAtInfty ENNReal

/-- Near a continuous function, continuous functions are uniformly close on a compact set. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_eventually_unif
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (c₀ : C(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in 𝓝 c₀, ∀ x ∈ K, |c x - c₀ x| < ε := by
  have h := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
    (tendsto_id : Tendsto (fun c : C(X, ℝ) ↦ c) (𝓝 c₀) (𝓝 c₀))) K hK
  rw [Metric.tendstoUniformlyOn_iff] at h
  filter_upwards [h ε hε] with c hc x hx
  have := hc x hx
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this

/-- Pointwise evaluation of a function vanishing at infinity is bounded by its norm. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_c0_apply_le
    {X : Type*} [TopologicalSpace X] (g : C₀(X, ℝ)) (x : X) : |g x| ≤ ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, ← Real.norm_eq_abs]
  exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF x

/-- Evaluation of a function vanishing at infinity is continuous in the function. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_c0_continuous_eval
    {X : Type*} [TopologicalSpace X] (x : X) :
    Continuous fun g : C₀(X, ℝ) ↦ g x := by
  have h : Continuous fun g : BoundedContinuousFunction X ℝ ↦ g x := continuous_eval_const x
  exact h.comp ZeroAtInftyContinuousMap.isometry_toBCF.continuous

/-- **Continuity of the weighted mass pairing.** On a bounded measurable set, the pairing
`(ρ, g) ↦ ∫_U ρ g ψ` is continuous for `ψ` integrable on `U`, with `ρ` locally uniform and
`g` in the `C₀` norm. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_continuous_mass
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : IntegrableOn ψ U) :
    Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ↦
      ∫ x in U, q.1 x * q.2 x * ψ x := by
  rw [continuous_iff_continuousAt]
  rintro ⟨ρ₀, g₀⟩
  have hK : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn ρ₀.continuous.continuousOn
  have hnear : ∀ᶠ q in 𝓝 (ρ₀, g₀), (∀ x ∈ closure U, |q.1 x - ρ₀ x| < 1) ∧ ‖q.2 - g₀‖ < 1 := by
    have h1 := (continuous_fst.tendsto (ρ₀, g₀)).eventually
      (aux_finiteDimensional_cutoff_measurable_semigroup_eventually_unif hK ρ₀ one_pos)
    have h2 := (continuous_snd.tendsto (ρ₀, g₀)).eventually
      (Metric.ball_mem_nhds g₀ one_pos)
    filter_upwards [h1, h2] with q hq1 hq2
    exact ⟨hq1, by simpa [dist_eq_norm] using hq2⟩
  refine continuousAt_of_dominated (bound := fun x ↦ (M + 1) * (‖g₀‖ + 1) * |ψ x|) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun q ↦ ?_
    exact ((q.1.continuous.mul q.2.continuous).aestronglyMeasurable).mul
      hψ.aestronglyMeasurable
  · filter_upwards [hnear] with q hq
    filter_upwards [ae_restrict_mem hU] with x hx
    have hxK : x ∈ closure U := subset_closure hx
    have hρ : |q.1 x| ≤ M + 1 := by
      have h1 := hq.1 x hxK
      have h2 : |ρ₀ x| ≤ M := by simpa [Real.norm_eq_abs] using hM x hxK
      calc |q.1 x| = |(q.1 x - ρ₀ x) + ρ₀ x| := by ring_nf
        _ ≤ |q.1 x - ρ₀ x| + |ρ₀ x| := abs_add_le _ _
        _ ≤ M + 1 := by linarith
    have hg : |q.2 x| ≤ ‖g₀‖ + 1 := by
      have h1 := aux_finiteDimensional_cutoff_measurable_semigroup_c0_apply_le q.2 x
      have h2 : ‖q.2‖ ≤ ‖g₀‖ + 1 := by
        calc ‖q.2‖ = ‖(q.2 - g₀) + g₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖q.2 - g₀‖ + ‖g₀‖ := norm_add_le _ _
          _ ≤ ‖g₀‖ + 1 := by linarith [hq.2]
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hψ0 : 0 ≤ |ψ x| := abs_nonneg _
    have hg0 : 0 ≤ |q.2 x| := abs_nonneg _
    have hM1 : 0 ≤ M + 1 := le_trans (abs_nonneg _) hρ
    calc |q.1 x| * |q.2 x| * |ψ x| ≤ (M + 1) * |q.2 x| * |ψ x| := by
          gcongr
      _ ≤ (M + 1) * (‖g₀‖ + 1) * |ψ x| := by gcongr
  · exact (hψ.norm.const_mul ((M + 1) * (‖g₀‖ + 1))).congr
      (Eventually.of_forall fun x ↦ by simp [Real.norm_eq_abs])
  · refine Eventually.of_forall fun x ↦ ?_
    have h1 : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ↦ q.1 x :=
      (continuous_eval_const x).comp continuous_fst
    have h2 : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ↦ q.2 x :=
      (aux_finiteDimensional_cutoff_measurable_semigroup_c0_continuous_eval x).comp
        continuous_snd
    exact ((h1.mul h2).mul continuous_const).continuousAt

/-- A continuous multiplier of an `L²(U)` function on a bounded set, as an `L²` element. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_mulLp
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) (c : C(Fin d → ℝ, ℝ)) :
    Lp ℝ 2 (volume.restrict U) :=
  (show MemLp (fun x ↦ c x * ψ x) 2 (volume.restrict U) by
    obtain ⟨C, hC⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn
      c.continuous.continuousOn
    refine hψ.of_le_mul (c := C) (c.continuous.aestronglyMeasurable.mul
      hψ.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x (subset_closure hx)) (norm_nonneg _)).toLp _

theorem aux_finiteDimensional_cutoff_measurable_semigroup_mulLp_ae
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) (c : C(Fin d → ℝ, ℝ)) :
    (aux_finiteDimensional_cutoff_measurable_semigroup_mulLp hU hUb hψ c :
        (Fin d → ℝ) → ℝ) =ᵐ[volume.restrict U] fun x ↦ c x * ψ x :=
  MemLp.coeFn_toLp _

/-- The continuous multiplier map into `L²(U)` is continuous for locally uniform convergence. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_continuous_mulLp
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) :
    Continuous (aux_finiteDimensional_cutoff_measurable_semigroup_mulLp hU hUb hψ) := by
  rw [continuous_iff_continuousAt]
  intro c₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set L : ℝ := (eLpNorm ψ 2 (volume.restrict U)).toReal with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (2 * (L + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  filter_upwards [aux_finiteDimensional_cutoff_measurable_semigroup_eventually_unif
    hUb.isCompact_closure c₀ hδ0] with c hc
  rw [Lp.dist_edist, aux_finiteDimensional_cutoff_measurable_semigroup_mulLp,
    aux_finiteDimensional_cutoff_measurable_semigroup_mulLp, Lp.edist_toLp_toLp]
  have hbound : eLpNorm ((fun x ↦ c x * ψ x) - fun x ↦ c₀ x * ψ x) 2 (volume.restrict U) ≤
      eLpNorm (δ • ψ) 2 (volume.restrict U) := by
    refine eLpNorm_mono_ae
      ((c.continuous.aestronglyMeasurable.mul hψ.aestronglyMeasurable).sub
        (c₀.continuous.aestronglyMeasurable.mul hψ.aestronglyMeasurable)) ?_
    filter_upwards [ae_restrict_mem hU] with x hx
    have h := (hc x (subset_closure hx)).le
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    rw [← sub_mul, abs_mul, abs_mul, abs_of_pos hδ0]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
  rw [eLpNorm_const_smul] at hbound
  have hfin : eLpNorm ψ 2 (volume.restrict U) ≠ ⊤ := hψ.eLpNorm_ne_top
  have hle := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) hbound
  rw [ENNReal.toReal_mul] at hle
  simp only [ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hδ0] at hle
  rw [← hL] at hle
  calc _ ≤ δ * L := hle
    _ < ε := by
        rw [hδ]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        exact mul_lt_mul_of_pos_left (by linarith) hε

/-- The weighted gradient pairing is an `L²` inner product. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_integral_eq_inner
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) (c : C(Fin d → ℝ, ℝ))
    (G : Lp ℝ 2 (volume.restrict U)) :
    ∫ x in U, c x * (G : (Fin d → ℝ) → ℝ) x * ψ x =
      inner ℝ G (aux_finiteDimensional_cutoff_measurable_semigroup_mulLp hU hUb hψ c) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [aux_finiteDimensional_cutoff_measurable_semigroup_mulLp_ae hU hUb hψ c]
    with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **Continuity of the weighted gradient pairing** in the coefficient (locally uniformly) and
the gradient component (in `L²(U)`). -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_continuous_grad
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) :
    Continuous fun q : C(Fin d → ℝ, ℝ) × Lp ℝ 2 (volume.restrict U) ↦
      ∫ x in U, q.1 x * (q.2 : (Fin d → ℝ) → ℝ) x * ψ x := by
  have h : Continuous fun q : C(Fin d → ℝ, ℝ) × Lp ℝ 2 (volume.restrict U) ↦
      inner ℝ q.2 (aux_finiteDimensional_cutoff_measurable_semigroup_mulLp hU hUb hψ q.1) :=
    continuous_snd.inner
      ((aux_finiteDimensional_cutoff_measurable_semigroup_continuous_mulLp hU hUb hψ).comp
        continuous_fst)
  refine h.congr fun q ↦ ?_
  exact (aux_finiteDimensional_cutoff_measurable_semigroup_integral_eq_inner
    hU hUb hψ q.1 q.2).symm

end aux_continuity

section aux_cubeRelation

open Filter MeasureTheory Topology Set
open scoped ZeroAtInfty ENNReal

open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

/-- The gradient vector field of an `L²` gradient family. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_gradField {d : ℕ} {U : Set (Fin d → ℝ)}
    (G : Fin d → Lp ℝ 2 (volume.restrict U)) : (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x i ↦ (G i : (Fin d → ℝ) → ℝ) x

/-- **The weak massive relation on one centred cube**, with the weak gradient parametrized by an
`L²` family: `G` is a weak gradient of `g` on the cube, and `(g, G)` satisfies the massive
equation `μ ρ g − ∇·(c ∇g) = ρ f` against every `H¹₀` test. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel (d k : ℕ) (mu : ℝ)
    (f : C₀(Fin d → ℝ, ℝ)) (c rho : (Fin d → ℝ) → ℝ) (g : C₀(Fin d → ℝ, ℝ))
    (G : Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) : Prop :=
  Homogenization.HasWeakGradientOn (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) (fun x ↦ g x)
      (aux_finiteDimensional_cutoff_measurable_semigroup_gradField G) ∧
    ∀ φ : Homogenization.H10Function (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)),
      mu * ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          rho x * g x * φ.toH1Function.toFun x ∂volume +
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          Homogenization.vecDot
            (c x • aux_finiteDimensional_cutoff_measurable_semigroup_gradField G x)
            (φ.toH1Function.grad x) ∂volume =
      ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
        rho x * f x * φ.toH1Function.toFun x ∂volume

/-- The `H¹` function with value function `g` and gradient field `G`. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_mkH1 {d k : ℕ} (g : C₀(Fin d → ℝ, ℝ))
    (G : Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))))
    (hG : Homogenization.HasWeakGradientOn (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))
      (fun x ↦ g x) (aux_finiteDimensional_cutoff_measurable_semigroup_gradField G)) :
    Homogenization.H1Function (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) where
  toFun x := g x
  grad := aux_finiteDimensional_cutoff_measurable_semigroup_gradField G
  memL2 := memL2On_of_zeroAtInfty
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)) g
  gradMemL2 i := Lp.memLp (G i)
  hasWeakGradient := hG

/-- A relation witness is a weak solution of the massive equation. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel_solution {d k : ℕ} {mu : ℝ}
    {f : C₀(Fin d → ℝ, ℝ)} {c rho : (Fin d → ℝ) → ℝ} {g : C₀(Fin d → ℝ, ℝ)}
    {G : Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))}
    (h : aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel d k mu f c rho g G) :
    IsMassiveWeakSolutionOn c rho mu (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))
      (aux_finiteDimensional_cutoff_measurable_semigroup_mkH1 g G h.1) (fun x ↦ f x) :=
  h.2

/-- **Existence of a relation witness** from a weak elliptic resolvent datum. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel_of_weak {d : ℕ}
    {c rho : (Fin d → ℝ) → ℝ} {D : C0ResolventDatum (Fin d → ℝ)}
    (hD : IsWeakEllipticResolvent c rho D) (mu : MarkovProcess.Semigroup.PositiveShift)
    (f : C₀(Fin d → ℝ, ℝ)) (k : ℕ) :
    ∃ G, aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel d k (mu : ℝ) f c rho
      (D.solution mu f) G := by
  have hW := SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  have hUm : MeasurableSet (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) := hW.isOpen.measurableSet
  obtain ⟨u, hu, husol⟩ := hD mu f _ hW
  let G : Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))) :=
    fun i ↦ (u.gradMemL2 i).toLp _
  have hGae : ∀ i, (G i : (Fin d → ℝ) → ℝ) =ᵐ[volume.restrict
      (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))] fun x ↦ u.grad x i :=
    fun i ↦ MemLp.coeFn_toLp _
  have hGall : ∀ᵐ x ∂(volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))),
      aux_finiteDimensional_cutoff_measurable_semigroup_gradField G x = u.grad x := by
    filter_upwards [ae_all_iff.2 hGae] with x hx
    funext i
    exact hx i
  refine ⟨G, ?_, ?_⟩
  · intro i φ hφ hφc hφs
    have h1 := u.hasWeakGradient i φ hφ hφc hφs
    have hl : ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
        D.solution mu f x * (fderiv ℝ φ x) (Homogenization.basisVec i) ∂volume =
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          u.toFun x * (fderiv ℝ φ x) (Homogenization.basisVec i) ∂volume := by
      refine setIntegral_congr_fun hUm fun x hx ↦ ?_
      simp only [hu x hx]
    have hr : ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
        aux_finiteDimensional_cutoff_measurable_semigroup_gradField G x i * φ x ∂volume =
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ), u.grad x i * φ x ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [hGall] with x hx
      rw [hx]
    simp only at h1 ⊢
    rw [hl, hr]
    exact h1
  · intro φ
    have h1 := husol φ
    have hl : ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
        rho x * D.solution mu f x * φ.toH1Function.toFun x ∂volume =
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          rho x * u.toFun x * φ.toH1Function.toFun x ∂volume := by
      refine setIntegral_congr_fun hUm fun x hx ↦ ?_
      simp only [hu x hx]
    have hr : ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
        Homogenization.vecDot
          (c x • aux_finiteDimensional_cutoff_measurable_semigroup_gradField G x)
          (φ.toH1Function.grad x) ∂volume =
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          Homogenization.vecDot (c x • u.grad x) (φ.toH1Function.grad x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [hGall] with x hx
      rw [hx]
    rw [hl, hr]
    exact h1

/-- The origin lies in every centred cube. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_zero_mem_cube (d n : ℕ) :
    (0 : Fin d → ℝ) ∈ SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ) := by
  rw [SubdiffusiveProcess.CoarseGrainingVocab.cube, Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hhalf : (0 : ℝ) < (1 / 2) * (3 : ℝ) ^ (n : ℤ) := by positivity
  constructor
  · simp only [Pi.zero_apply]
    linarith
  · simp only [Pi.zero_apply]
    linarith

/-- A continuous function attains its minimum and maximum on the closure of a centred cube. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_cube_extrema {d : ℕ}
    {c : (Fin d → ℝ) → ℝ} (hc : Continuous c) (n : ℕ) :
    (∃ x ∈ closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ)),
      IsMinOn c (closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ))) x) ∧
    (∃ x ∈ closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ)),
      IsMaxOn c (closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ))) x) := by
  have hK : IsCompact (closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ))) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
      ).isBoundedDomain.isBounded.isCompact_closure
  have hne : (closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ))).Nonempty :=
    ⟨0, subset_closure (aux_finiteDimensional_cutoff_measurable_semigroup_zero_mem_cube d n)⟩
  exact ⟨hK.exists_isMinOn hne hc.continuousOn, hK.exists_isMaxOn hne hc.continuousOn⟩

/-- Continuous positive coefficients have the local cube bounds used by whole-space uniqueness. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_cube_bounds
    {d : ℕ} {c rho : (Fin d → ℝ) → ℝ}
    (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    (hrho : Continuous rho) (hrhopos : ∀ x, 0 < rho x) :
    Nonempty (MassiveCubeBounds c rho) := by
  choose xmin hxmin hmin using fun n ↦
    (aux_finiteDimensional_cutoff_measurable_semigroup_cube_extrema hc n).1
  choose xmax hxmax hmax using fun n ↦
    (aux_finiteDimensional_cutoff_measurable_semigroup_cube_extrema hc n).2
  choose rmin hrmin hrmin' using fun n ↦
    (aux_finiteDimensional_cutoff_measurable_semigroup_cube_extrema hrho n).1
  choose rmax hrmax hrmax' using fun n ↦
    (aux_finiteDimensional_cutoff_measurable_semigroup_cube_extrema hrho n).2
  let B : MassiveCubeBounds c rho :=
    { lam := fun n ↦ c (xmin n), Lam := fun n ↦ c (xmax n),
      rhoMin := fun n ↦ rho (rmin n), rhoMax := fun n ↦ rho (rmax n),
      lam_pos := fun n ↦ hcpos (xmin n),
      rhoMin_pos := fun n ↦ hrhopos (rmin n), ell := by
        intro n
        apply SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
            (n : ℤ)).isOpen.measurableSet
          hc.continuousOn (hcpos (xmin n))
        intro x hx
        exact ⟨hmin n (subset_closure hx), hmax n (subset_closure hx)⟩,
      coeff_lower := by
        intro n x hx
        exact hmin n (subset_closure hx),
      rho_measurable := by
        intro n
        exact hrho.aestronglyMeasurable,
      rho_lower := by
        intro n x hx
        exact hrmin' n (subset_closure hx),
      rho_bounded := by
        intro n
        filter_upwards [ae_restrict_mem
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
            (n : ℤ)).isOpen.measurableSet] with x hx
        rw [abs_of_pos (hrhopos x)]
        exact hrmax' n (subset_closure hx) }
  exact ⟨B⟩

/-- **Uniqueness of the relation section** under local cube bounds: two `C₀` functions carrying
relation witnesses on every centred cube coincide. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel_unique {d : ℕ} {mu : ℝ}
    (hmu : 0 < mu) {f : C₀(Fin d → ℝ, ℝ)} {c rho : (Fin d → ℝ) → ℝ}
    (B : MassiveCubeBounds c rho) {g g' : C₀(Fin d → ℝ, ℝ)}
    (h : ∀ k, ∃ G, aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel d k mu f c rho g G)
    (h' : ∀ k, ∃ G,
      aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel d k mu f c rho g' G) :
    g = g' := by
  have hdecay : Tendsto (fun x ↦ g x - g' x) (cocompact (Fin d → ℝ)) (𝓝 0) := by
    have := zero_at_infty (g - g')
    simpa using! this
  have hzero := eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact B hmu
    (u := fun x ↦ g x - g' x) (g.continuous.sub g'.continuous) hdecay (fun k ↦ by
      have hW := SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube
        d (k : ℤ)
      obtain ⟨G, hG⟩ := h k
      obtain ⟨G', hG'⟩ := h' k
      have hs := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k) (B.rho_bounded k)
        (memL2On_of_zeroAtInfty hW f) (memL2On_of_zeroAtInfty hW f)
        (aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel_solution hG)
        (aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel_solution hG')
      refine ⟨aux_finiteDimensional_cutoff_measurable_semigroup_mkH1 g G hG.1 -
          aux_finiteDimensional_cutoff_measurable_semigroup_mkH1 g' G' hG'.1,
        Eventually.of_forall fun x ↦ ?_, IsMassiveWeakSolutionOn.congr_forcing ?_ hs⟩
      · simp [Homogenization.H1Function.sub_toFun, aux_finiteDimensional_cutoff_measurable_semigroup_mkH1]
      · funext x
        simp)
  ext x
  exact sub_eq_zero.1 (hzero x)

end aux_cubeRelation

section aux_closedness

open Filter MeasureTheory Topology Set
open scoped ZeroAtInfty ENNReal

open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

/-- The coefficient profile `y ↦ a e^{y - z}`. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_coefFun (a z : ℝ) : C(ℝ, ℝ) :=
  ⟨fun y ↦ a * Real.exp (y - z), by fun_prop⟩

/-- The speed profile `y ↦ e^{y - z}`. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_rhoFun (z : ℝ) : C(ℝ, ℝ) :=
  ⟨fun y ↦ Real.exp (y - z), by fun_prop⟩

/-- A continuous function is integrable against an `L²` function on a bounded set. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_integrable_grad_term
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) (c : C(Fin d → ℝ, ℝ))
    (G : Lp ℝ 2 (volume.restrict U)) :
    Integrable (fun x ↦ c x * (G : (Fin d → ℝ) → ℝ) x * ψ x) (volume.restrict U) := by
  refine (L2.integrable_inner (𝕜 := ℝ) G
    (aux_finiteDimensional_cutoff_measurable_semigroup_mulLp hU hUb hψ c)).congr ?_
  filter_upwards [aux_finiteDimensional_cutoff_measurable_semigroup_mulLp_ae hU hUb hψ c]
    with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The gradient term of the weak equation splits into coordinate `L²` pairings. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_integral_vecDot
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {Ψ : (Fin d → ℝ) → (Fin d → ℝ)} (hΨ : ∀ i, MemLp (fun x ↦ Ψ x i) 2 (volume.restrict U))
    (c : C(Fin d → ℝ, ℝ)) (G : Fin d → Lp ℝ 2 (volume.restrict U)) :
    ∫ x in U, Homogenization.vecDot
        (c x • aux_finiteDimensional_cutoff_measurable_semigroup_gradField G x) (Ψ x) ∂volume =
      ∑ i, ∫ x in U, c x * (G i : (Fin d → ℝ) → ℝ) x * Ψ x i := by
  rw [← integral_finsetSum _ fun i _ ↦
    aux_finiteDimensional_cutoff_measurable_semigroup_integrable_grad_term hU hUb (hΨ i) c (G i)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Homogenization.vecDot, aux_finiteDimensional_cutoff_measurable_semigroup_gradField,
    Pi.smul_apply, smul_eq_mul]

/-- **The relation set on one cube is closed** in the Polish product of potentials, `C₀`
values and `L²` gradient families. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_isClosed_cubeRel
    (d k : ℕ) (a z mu : ℝ) (f : C₀(Fin d → ℝ, ℝ)) :
    IsClosed {q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
        (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) |
      aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel d k mu f
        ((aux_finiteDimensional_cutoff_measurable_semigroup_coefFun a z).comp q.1)
        ((aux_finiteDimensional_cutoff_measurable_semigroup_rhoFun z).comp q.1) q.2.1 q.2.2} := by
  have hW := SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  have hU : MeasurableSet (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) := hW.isOpen.measurableSet
  have hUb : Bornology.IsBounded (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) :=
    hW.isBoundedDomain.isBounded
  have : IsFiniteMeasure (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))) :=
    hW.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hcoef : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
      (aux_finiteDimensional_cutoff_measurable_semigroup_coefFun a z).comp q.1 :=
    (ContinuousMap.continuous_postcomp _).comp continuous_fst
  have hrho : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
      (aux_finiteDimensional_cutoff_measurable_semigroup_rhoFun z).comp q.1 :=
    (ContinuousMap.continuous_postcomp _).comp continuous_fst
  -- weak-gradient conditions
  have hWG : IsClosed {q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) |
      Homogenization.HasWeakGradientOn (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))
        (fun x ↦ q.2.1 x) (aux_finiteDimensional_cutoff_measurable_semigroup_gradField q.2.2)} := by
    simp only [Homogenization.HasWeakGradientOn, Homogenization.HasWeakPartialDerivOn,
      ofPred_forall]
    refine isClosed_iInter fun i ↦ isClosed_iInter fun φ ↦ isClosed_iInter fun hφ ↦
      isClosed_iInter fun hφc ↦ isClosed_iInter fun _ ↦ isClosed_eq ?_ ?_
    · have hψ : IntegrableOn (fun x ↦ (fderiv ℝ φ x) (Homogenization.basisVec i))
          (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) := by
        have hcont : Continuous fun x ↦ (fderiv ℝ φ x) (Homogenization.basisVec i) :=
          (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
        have hcs : HasCompactSupport fun x ↦ (fderiv ℝ φ x) (Homogenization.basisVec i) :=
          hφc.fderiv_apply (𝕜 := ℝ) _
        exact (hcont.integrable_of_hasCompactSupport hcs).integrableOn
      have hg : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
          (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
          ((1 : C(Fin d → ℝ, ℝ)), q.2.1) :=
        continuous_const.prodMk (continuous_fst.comp continuous_snd)
      have h := (aux_finiteDimensional_cutoff_measurable_semigroup_continuous_mass
        hU hUb hψ).comp hg
      refine h.congr fun q ↦ ?_
      simp
    · have hψ : MemLp φ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))) :=
        (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict _
      have hGi : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
          (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
          ((1 : C(Fin d → ℝ, ℝ)), q.2.2 i) :=
        continuous_const.prodMk ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
      have h := (aux_finiteDimensional_cutoff_measurable_semigroup_continuous_grad
        hU hUb hψ).comp hGi
      refine (h.neg).congr fun q ↦ ?_
      simp [aux_finiteDimensional_cutoff_measurable_semigroup_gradField]
  -- equation conditions
  have hEQ : IsClosed {q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) |
      ∀ φ : Homogenization.H10Function (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)),
        mu * ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
            (aux_finiteDimensional_cutoff_measurable_semigroup_rhoFun z).comp q.1 x * q.2.1 x *
              φ.toH1Function.toFun x ∂volume +
          ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
            Homogenization.vecDot
              ((aux_finiteDimensional_cutoff_measurable_semigroup_coefFun a z).comp q.1 x •
                aux_finiteDimensional_cutoff_measurable_semigroup_gradField q.2.2 x)
              (φ.toH1Function.grad x) ∂volume =
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          (aux_finiteDimensional_cutoff_measurable_semigroup_rhoFun z).comp q.1 x * f x *
            φ.toH1Function.toFun x ∂volume} := by
    simp only [ofPred_forall]
    refine isClosed_iInter fun φ ↦ isClosed_eq ?_ ?_
    · have hψ : IntegrableOn φ.toH1Function.toFun (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) :=
        φ.toH1Function.memL2.integrable one_le_two
      have hmass := (aux_finiteDimensional_cutoff_measurable_semigroup_continuous_mass
        hU hUb hψ).comp (hrho.prodMk (continuous_fst.comp continuous_snd))
      have hgrad : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
          (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
          ∑ i, ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
            (aux_finiteDimensional_cutoff_measurable_semigroup_coefFun a z).comp q.1 x *
              (q.2.2 i : (Fin d → ℝ) → ℝ) x * φ.toH1Function.grad x i := by
        refine continuous_finsetSum _ fun i _ ↦ ?_
        have hGi : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
            (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
            ((aux_finiteDimensional_cutoff_measurable_semigroup_coefFun a z).comp q.1, q.2.2 i) :=
          hcoef.prodMk ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
        exact (aux_finiteDimensional_cutoff_measurable_semigroup_continuous_grad hU hUb
          (φ.toH1Function.gradMemL2 i)).comp hGi
      refine (((continuous_const (y := mu)).mul hmass).add hgrad).congr fun q ↦ ?_
      simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply]
      rw [aux_finiteDimensional_cutoff_measurable_semigroup_integral_vecDot hU hUb
        φ.toH1Function.gradMemL2]
    · have hψ : IntegrableOn φ.toH1Function.toFun (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) :=
        φ.toH1Function.memL2.integrable one_le_two
      exact (aux_finiteDimensional_cutoff_measurable_semigroup_continuous_mass
        hU hUb hψ).comp (hrho.prodMk continuous_const)
  exact hWG.inter hEQ

end aux_closedness

section aux_graph

open Filter MeasureTheory Topology Set
open scoped ZeroAtInfty ENNReal

open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

/-- The graph of the whole-space weak massive solution operator over potentials: `(p, g)` lies
in it when `g ∈ C₀` solves `μ ρ_p g − ∇·(c_p ∇g) = ρ_p f` weakly on every centred cube, with
`c_p = a e^{p - z}` and `ρ_p = e^{p - z}`. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_graph (d : ℕ) (a z mu : ℝ)
    (f : C₀(Fin d → ℝ, ℝ)) : Set (C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ)) :=
  {pg | ∀ k : ℕ, ∃ G, aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel d k mu f
    ((aux_finiteDimensional_cutoff_measurable_semigroup_coefFun a z).comp pg.1)
    ((aux_finiteDimensional_cutoff_measurable_semigroup_rhoFun z).comp pg.1) pg.2 G}

theorem aux_finiteDimensional_cutoff_measurable_semigroup_potential_polish (d : ℕ) :
    PolishSpace C(Fin d → ℝ, ℝ) := by
  let : TopologicalSpace.IsCompletelyMetrizableSpace C(Fin d → ℝ, ℝ) :=
    TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
      (X := C(Fin d → ℝ, ℝ))
  infer_instance

/-- **The solution graph is analytic**: it is a countable intersection of projections of closed
subsets of Polish spaces. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_analytic_graph (d : ℕ) (a z mu : ℝ)
    (f : C₀(Fin d → ℝ, ℝ)) :
    AnalyticSet (aux_finiteDimensional_cutoff_measurable_semigroup_graph d a z mu f) := by
  have := aux_finiteDimensional_cutoff_measurable_semigroup_potential_polish d
  have := aux_finiteDimensional_cutoff_measurable_semigroup_c0_polish d
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have heq : aux_finiteDimensional_cutoff_measurable_semigroup_graph d a z mu f =
      ⋂ k : ℕ, (fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
          (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
          (q.1, q.2.1)) ''
        {q | aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel d k mu f
          ((aux_finiteDimensional_cutoff_measurable_semigroup_coefFun a z).comp q.1)
          ((aux_finiteDimensional_cutoff_measurable_semigroup_rhoFun z).comp q.1)
          q.2.1 q.2.2} := by
    ext ⟨p, g⟩
    simp only [aux_finiteDimensional_cutoff_measurable_semigroup_graph, mem_ofPred_eq,
      mem_iInter, mem_image, Prod.exists, Prod.mk.injEq]
    constructor
    · intro h k
      obtain ⟨G, hG⟩ := h k
      exact ⟨p, g, G, hG, rfl, rfl⟩
    · intro h k
      obtain ⟨p', g', G, hG, rfl, rfl⟩ := h k
      exact ⟨G, hG⟩
  rw [heq]
  refine AnalyticSet.iInter fun k ↦ ?_
  have hL2 : SecondCountableTopology
      (Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) := inferInstance
  have : SecondCountableTopology
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) :=
    inferInstance
  have : PolishSpace
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) :=
    inferInstance
  exact (aux_finiteDimensional_cutoff_measurable_semigroup_isClosed_cubeRel d k a z mu f
    ).analyticSet.image_of_continuous (continuous_fst.prodMk (continuous_fst.comp continuous_snd))

/-- The solution graph is single-valued over every potential. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_graph_unique {d : ℕ} {a z mu : ℝ}
    (ha : 0 < a) (hmu : 0 < mu) (f : C₀(Fin d → ℝ, ℝ)) (p : C(Fin d → ℝ, ℝ))
    (g g' : C₀(Fin d → ℝ, ℝ))
    (hg : (p, g) ∈ aux_finiteDimensional_cutoff_measurable_semigroup_graph d a z mu f)
    (hg' : (p, g') ∈ aux_finiteDimensional_cutoff_measurable_semigroup_graph d a z mu f) :
    g = g' := by
  obtain ⟨B⟩ := aux_finiteDimensional_cutoff_measurable_semigroup_cube_bounds
    (c := (aux_finiteDimensional_cutoff_measurable_semigroup_coefFun a z).comp p)
    (rho := (aux_finiteDimensional_cutoff_measurable_semigroup_rhoFun z).comp p)
    (ContinuousMap.continuous _) (fun x ↦ mul_pos ha (Real.exp_pos _))
    (ContinuousMap.continuous _) (fun x ↦ Real.exp_pos _)
  exact aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel_unique hmu B hg hg'

/-- **Measurability of the canonical resolvent section.** A map carrying every parameter of a
set `G` to the (unique) `C₀` weak solution over a measurable potential is measurable on `G`. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_measurable_section {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C(Fin d → ℝ, ℝ)] [BorelSpace C(Fin d → ℝ, ℝ)]
    {a z mu : ℝ} (ha : 0 < a) (hmu : 0 < mu) (f : C₀(Fin d → ℝ, ℝ))
    (Pot : Ω → C(Fin d → ℝ, ℝ)) (hPot : Measurable Pot) (G : Set Ω)
    (s : Ω → C₀(Fin d → ℝ, ℝ))
    (hs : ∀ ω ∈ G, (Pot ω, s ω) ∈ aux_finiteDimensional_cutoff_measurable_semigroup_graph d a z mu f) :
    @Measurable G C₀(Fin d → ℝ, ℝ) _ (borel _) fun ω ↦ s ω := by
  let : MeasurableSpace C₀(Fin d → ℝ, ℝ) := borel _
  have : BorelSpace C₀(Fin d → ℝ, ℝ) := ⟨rfl⟩
  have := aux_finiteDimensional_cutoff_measurable_semigroup_potential_polish d
  have := aux_finiteDimensional_cutoff_measurable_semigroup_c0_polish d
  exact aux_finiteDimensional_cutoff_measurable_semigroup_measurable_of_analytic
    (aux_finiteDimensional_cutoff_measurable_semigroup_graph d a z mu f)
    (aux_finiteDimensional_cutoff_measurable_semigroup_analytic_graph d a z mu f)
    (aux_finiteDimensional_cutoff_measurable_semigroup_graph_unique ha hmu f)
    Pot hPot G s hs

end aux_graph

section aux_identification

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal ZeroAtInfty

/-- The cutoff potential `H ω + ∑_{j ≤ N} ω(-j)` as a continuous map. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_potential {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d) :
    C(SpatialCoordinates d, ℝ) :=
  H omega + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j))

theorem aux_finiteDimensional_cutoff_measurable_semigroup_potential_apply {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d)
    (x : SpatialCoordinates d) :
    aux_finiteDimensional_cutoff_measurable_semigroup_potential H N omega x =
      cutoffPotential H omega N x := by
  simp [aux_finiteDimensional_cutoff_measurable_semigroup_potential, cutoffPotential,
    ContinuousMap.sum_apply]

theorem aux_finiteDimensional_cutoff_measurable_semigroup_measurable_potential {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : Measurable H) (N : ℕ) :
    Measurable (aux_finiteDimensional_cutoff_measurable_semigroup_potential H N) := by
  unfold aux_finiteDimensional_cutoff_measurable_semigroup_potential
  exact hH.add (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply _)

theorem aux_finiteDimensional_cutoff_measurable_semigroup_coef_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    cutoffCoefficient M H omega N =
      ⇑((aux_finiteDimensional_cutoff_measurable_semigroup_coefFun
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹
          ((N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)).comp
        (aux_finiteDimensional_cutoff_measurable_semigroup_potential H N omega)) := by
  funext x
  simp [cutoffCoefficient, aux_finiteDimensional_cutoff_measurable_semigroup_coefFun,
    aux_finiteDimensional_cutoff_measurable_semigroup_potential_apply]

theorem aux_finiteDimensional_cutoff_measurable_semigroup_rho_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    cutoffSpeedDensity M H omega N =
      ⇑((aux_finiteDimensional_cutoff_measurable_semigroup_rhoFun
          ((N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)).comp
        (aux_finiteDimensional_cutoff_measurable_semigroup_potential H N omega)) := by
  funext x
  simp [cutoffSpeedDensity, aux_finiteDimensional_cutoff_measurable_semigroup_rhoFun,
    aux_finiteDimensional_cutoff_measurable_semigroup_potential_apply]

/-- **Identification step.** The resolvent of a Feller family member whose Laplace transform is a
weak elliptic resolvent datum for the actual cutoff coefficients lies on the solution graph. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_resolvent_mem_graph {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    {Q : SubMarkovKernelSemigroup (SpatialCoordinates d)} (hQ : Q.IsFellerKernelSemigroup)
    (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (SpatialCoordinates d))
    (hDweak : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
      (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D)
    (hDlap : ∀ (mu : Semigroup.PositiveShift)
      (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      D.solution mu f x =
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
          kernelIntegral (Q (Real.toNNReal t)) f x)
    (mu : Semigroup.PositiveShift) (f : C₀(SpatialCoordinates d, ℝ)) :
    (aux_finiteDimensional_cutoff_measurable_semigroup_potential H N omega,
      hQ.c0Semigroup.toContractiveResolvent.operator mu f) ∈
      aux_finiteDimensional_cutoff_measurable_semigroup_graph d
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹
        ((N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) (mu : ℝ) f := by
  have heq : hQ.c0Semigroup.toContractiveResolvent.operator mu f = D.solution mu f := by
    ext x
    rw [Semigroup.StronglyContinuousContractionSemigroup.toContractiveResolvent_operator,
      hQ.resolvent_apply_apply, hDlap]
  rw [heq]
  intro k
  have h := aux_finiteDimensional_cutoff_measurable_semigroup_cubeRel_of_weak hDweak mu f k
  rw [aux_finiteDimensional_cutoff_measurable_semigroup_coef_eq,
    aux_finiteDimensional_cutoff_measurable_semigroup_rho_eq] at h
  exact h

end aux_identification

section aux_orbits

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal ZeroAtInfty

/-- **Orbit measurability on the identification event.** On a set of environments where every
member of the Feller family has a weak elliptic resolvent datum for the actual cutoff
coefficients as its Laplace transform, every transition integral of a `C₀` observable is
measurable in the environment. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_measurable_orbit {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : Measurable H) (N : ℕ)
    (Q : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hQ : ∀ omega, (Q omega).IsFellerKernelSemigroup) (G : Set (BilateralField d))
    (hG : ∀ omega ∈ G, ∃ D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
        (SpatialCoordinates d),
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
        (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
      ∀ (mu : Semigroup.PositiveShift)
        (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
        D.solution mu f x =
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
            kernelIntegral (Q omega (Real.toNNReal t)) f x)
    (t : NNReal) (f : C₀(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) :
    Measurable fun omega : G ↦ kernelIntegral (Q omega t) f x := by
  let : MeasurableSpace C₀(SpatialCoordinates d, ℝ) := borel _
  have : BorelSpace C₀(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  have := aux_finiteDimensional_cutoff_measurable_semigroup_c0_secondCountable d
  have ha : 0 < (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ :=
    inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  have hR : ∀ (mu : Semigroup.PositiveShift) (g : C₀(SpatialCoordinates d, ℝ)),
      Measurable fun omega : G ↦ (hQ omega).c0Semigroup.toContractiveResolvent.operator mu g := by
    intro mu g
    refine aux_finiteDimensional_cutoff_measurable_semigroup_measurable_section
      (z := (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ha mu.2 g
      (aux_finiteDimensional_cutoff_measurable_semigroup_potential H N)
      (aux_finiteDimensional_cutoff_measurable_semigroup_measurable_potential hH N) G
      (fun omega ↦ (hQ omega).c0Semigroup.toContractiveResolvent.operator mu g) ?_
    intro omega homega
    obtain ⟨D, hDweak, hDlap⟩ := hG omega homega
    exact aux_finiteDimensional_cutoff_measurable_semigroup_resolvent_mem_graph M H omega N
      (hQ omega) D hDweak hDlap mu g
  have hgen := aux_finiteDimensional_cutoff_measurable_semigroup_measurable_generated
    (fun omega : G ↦ (hQ omega).c0Semigroup.toContractiveResolvent) hR t f
  simp only [Semigroup.StronglyContinuousContractionSemigroup.generatedSemigroup_toContractiveResolvent]
    at hgen
  have heval : Measurable fun g : C₀(SpatialCoordinates d, ℝ) ↦ g x :=
    (aux_finiteDimensional_cutoff_measurable_semigroup_c0_continuous_eval x).measurable
  exact heval.comp hgen

open Classical in
/-- **Joint measurability of the patched transition integrals.** Environment measurability on a
measurable set, together with joint continuity of Feller orbits in time and state, gives joint
measurability of the family patched by the identity off that set. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_measurable_patched_integral {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (Q : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hQ : ∀ omega, (Q omega).IsFellerKernelSemigroup) {G : Set (BilateralField d)}
    (hGm : MeasurableSet G)
    (horbit : ∀ (t : NNReal) (f : C₀(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d),
      Measurable fun omega : G ↦ kernelIntegral (Q omega t) f x)
    (f : C₀(SpatialCoordinates d, ℝ)) :
    Measurable fun q : BilateralField d × (NNReal × SpatialCoordinates d) ↦
      if q.1 ∈ G then kernelIntegral (Q q.1 q.2.1) f q.2.2 else f q.2.2 := by
  classical
  let u : NNReal × SpatialCoordinates d → BilateralField d → ℝ := fun tx omega ↦
    if omega ∈ G then kernelIntegral (Q omega tx.1) f tx.2 else f tx.2
  have hcont : ∀ omega, Continuous fun tx : NNReal × SpatialCoordinates d ↦ u tx omega := by
    intro omega
    by_cases h : omega ∈ G
    · simp only [u, h, ite_true]
      exact (hQ omega).c0Semigroup.continuous_apply_apply f
    · simp only [u, h, ite_false]
      exact f.continuous.comp continuous_snd
  have hmeas : ∀ tx, Measurable (u tx) := by
    intro tx
    refine measurable_of_restrict_of_restrict_compl hGm ?_ ?_
    · have h := horbit tx.1 f tx.2
      have heq : G.domRestrict (u tx) = fun omega : G ↦ kernelIntegral (Q omega tx.1) f tx.2 := by
        funext omega
        simp [u, Set.domRestrict, omega.2]
      rw [heq]
      exact h
    · have heq : Gᶜ.domRestrict (u tx) = fun _ : (Gᶜ : Set (BilateralField d)) ↦ f tx.2 := by
        funext omega
        have : (omega : BilateralField d) ∉ G := omega.2
        simp [u, Set.domRestrict, this]
      rw [heq]
      exact measurable_const
  have hjoint := measurable_uncurry_of_continuous_of_measurable hcont hmeas
  exact hjoint.comp (measurable_snd.prodMk measurable_fst)

end aux_orbits

section aux_patch

open scoped ZeroAtInfty

/-- A measurable full-measure set on which an almost-sure property holds everywhere. -/
theorem aux_finiteDimensional_cutoff_measurable_semigroup_exists_measurable_good
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : Ω → Prop} (h : ∀ᵐ ω ∂μ, p ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ᵐ ω ∂μ, ω ∈ G) ∧ ∀ ω ∈ G, p ω := by
  refine ⟨(toMeasurable μ {ω | ¬ p ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [ae_iff] at h ⊢
    simp only [Set.mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable]
    exact h
  · intro ω hω
    by_contra hp
    exact hω (subset_toMeasurable _ _ hp)

/-- The Feller family patched by the identity semigroup off a measurable event, jointly measurable
in environment, time and starting point once its orbits are measurable on the event. -/
def aux_finiteDimensional_cutoff_measurable_semigroup_patched {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (Q : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hQ : ∀ omega, (Q omega).IsFellerKernelSemigroup) {G : Set (BilateralField d)}
    (hGm : MeasurableSet G)
    (horbit : ∀ (t : NNReal) (f : C₀(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d),
      Measurable fun omega : G ↦ kernelIntegral (Q omega t) f x) :
    ParameterizedSubMarkovKernelSemigroup (BilateralField d) (SpatialCoordinates d) := by
  classical
  exact {
  kernel omega t := if omega ∈ G then Q omega t else Kernel.id
  measurable_kernel := by
    let μq : BilateralField d × (NNReal × SpatialCoordinates d) → Measure (SpatialCoordinates d) :=
      fun q ↦ (if q.1 ∈ G then Q q.1 q.2.1 else Kernel.id) q.2.2
    have hfin : ∀ q, IsFiniteMeasure (μq q) := by
      intro q
      by_cases h : q.1 ∈ G
      · have : IsFiniteKernel (Q q.1 q.2.1) := ((Q q.1).isSubMarkovKernel q.2.1).isFiniteKernel
        simp only [μq, h, ite_true]
        infer_instance
      · simp only [μq, h, ite_false, Kernel.id_apply]
        infer_instance
    have : ∀ q, (μq q).Regular := fun q ↦ inferInstance
    refine measurable_measure_of_measurable_integral_compactlySupported μq fun f ↦ ?_
    let f₀ : C₀(SpatialCoordinates d, ℝ) :=
      PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
    have hf₀ : ∀ y, f₀ y = f y := fun y ↦
      PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply f y
    have hmeas := aux_finiteDimensional_cutoff_measurable_semigroup_measurable_patched_integral
      Q hQ hGm horbit f₀
    have heq : (fun q ↦ ∫ x, f x ∂μq q) = fun q : BilateralField d × (NNReal × SpatialCoordinates d) ↦
        if q.1 ∈ G then kernelIntegral (Q q.1 q.2.1) f₀ q.2.2 else f₀ q.2.2 := by
      funext q
      by_cases h : q.1 ∈ G
      · simp only [μq, h, ite_true, kernelIntegral, hf₀]
      · simp only [μq, h, ite_false, Kernel.id_apply, hf₀]
        exact integral_dirac' _ _ f.continuous.stronglyMeasurable
    rw [heq]
    convert hmeas using 2
  kernel_zero omega := by
    by_cases h : omega ∈ G <;> simp [h, (Q omega).kernel_zero]
  kernel_add omega s t := by
    by_cases h : omega ∈ G
    · simp [h, (Q omega).kernel_add s t]
    · simp [h]
  isSubMarkovKernel omega t := by
    by_cases h : omega ∈ G
    · simpa [h] using (Q omega).isSubMarkovKernel t
    · simpa [h] using (IsSubMarkovKernel.id : IsSubMarkovKernel (Kernel.id :
        Kernel (SpatialCoordinates d) (SpatialCoordinates d)))
  }

theorem aux_finiteDimensional_cutoff_measurable_semigroup_patched_of_mem {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (Q : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hQ : ∀ omega, (Q omega).IsFellerKernelSemigroup) {G : Set (BilateralField d)}
    (hGm : MeasurableSet G)
    (horbit : ∀ (t : NNReal) (f : C₀(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d),
      Measurable fun omega : G ↦ kernelIntegral (Q omega t) f x)
    {omega : BilateralField d} (h : omega ∈ G) :
    (aux_finiteDimensional_cutoff_measurable_semigroup_patched Q hQ hGm horbit
      ).toSubMarkovKernelSemigroup omega = Q omega := by
  apply SubMarkovKernelSemigroup.ext
  intro t
  simp [aux_finiteDimensional_cutoff_measurable_semigroup_patched, h]

theorem aux_finiteDimensional_cutoff_measurable_semigroup_patched_of_not_mem {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (Q : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hQ : ∀ omega, (Q omega).IsFellerKernelSemigroup) {G : Set (BilateralField d)}
    (hGm : MeasurableSet G)
    (horbit : ∀ (t : NNReal) (f : C₀(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d),
      Measurable fun omega : G ↦ kernelIntegral (Q omega t) f x)
    {omega : BilateralField d} (h : omega ∉ G) :
    (aux_finiteDimensional_cutoff_measurable_semigroup_patched Q hQ hGm horbit
      ).toSubMarkovKernelSemigroup omega = MarkovProcess.idSemigroup := by
  apply SubMarkovKernelSemigroup.ext
  intro t
  simp [aux_finiteDimensional_cutoff_measurable_semigroup_patched, h, MarkovProcess.idSemigroup]

end aux_patch

/-- The measurable parameter version of the actual finite-cutoff transition
semigroups, from the SDE/weak-resolvent construction.
- All inputs are exactly those of finiteDimensional_cutoff_path_kernel;
  no measurability of the arbitrary displayed PN family is assumed.
- CONCLUDED: a jointly measurable version with the same fibres on one
  full event, conservative and Feller also on the exceptional complement.
- Build the canonical family from the actual cutoff coefficients and
  identify it with PN through their weak resolvents; choose the identity
  semigroup off a measurable full event. This identification is proof work.
- The parent retains continuous-path construction and FDD attachment;
  no path-kernel existence or moment criterion is added as a premise.
-/
theorem finiteDimensional_cutoff_measurable_semigroup
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d →
      SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hPNcons : ∀ N omega, (PN N omega).IsConservative)
    (hPNfeller : ∀ N omega, (PN N omega).IsFellerKernelSemigroup)
    (hres : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∃ D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
        (SpatialCoordinates d),
        (∀ mu, DenseRange (D.operator mu)) ∧
        SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
        ∀ (mu : Semigroup.PositiveShift)
          (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
          D.solution mu f x =
            ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
              kernelIntegral (PN N omega (Real.toNNReal t)) f x)
    (_hnonexplosion : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
        ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
            Homogenization.euclideanGradient
              (cutoffPotential H omega N) x‖ ≤
          K * (1 + ‖x‖)) :
    ∃ P : ℕ → ParameterizedSubMarkovKernelSemigroup
        (BilateralField d) (SpatialCoordinates d),
      (∀ N omega, ((P N).toSubMarkovKernelSemigroup omega).IsConservative) ∧
      (∀ N omega, ((P N).toSubMarkovKernelSemigroup omega).IsFellerKernelSemigroup) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ N, (P N).toSubMarkovKernelSemigroup omega = PN N omega := by
  classical
  obtain ⟨G, hGm, hGae, hGgood⟩ :=
    aux_finiteDimensional_cutoff_measurable_semigroup_exists_measurable_good hres
  have horbit : ∀ (N : ℕ) (t : NNReal) (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
      (x : SpatialCoordinates d), Measurable fun omega : G ↦ kernelIntegral (PN N omega t) f x := by
    intro N t f x
    refine aux_finiteDimensional_cutoff_measurable_semigroup_measurable_orbit M hH.1 N (PN N)
      (hPNfeller N) G (fun omega homega ↦ ?_) t f x
    obtain ⟨D, -, hDweak, hDlap⟩ := hGgood omega homega N
    exact ⟨D, hDweak, hDlap⟩
  refine ⟨fun N ↦ aux_finiteDimensional_cutoff_measurable_semigroup_patched (PN N)
    (hPNfeller N) hGm (horbit N), ?_, ?_, ?_⟩
  · intro N omega
    by_cases h : omega ∈ G
    · rw [aux_finiteDimensional_cutoff_measurable_semigroup_patched_of_mem _ _ _ _ h]
      exact hPNcons N omega
    · rw [aux_finiteDimensional_cutoff_measurable_semigroup_patched_of_not_mem _ _ _ _ h]
      exact MarkovProcess.isConservative_idSemigroup
  · intro N omega
    by_cases h : omega ∈ G
    · rw [aux_finiteDimensional_cutoff_measurable_semigroup_patched_of_mem _ _ _ _ h]
      exact hPNfeller N omega
    · rw [aux_finiteDimensional_cutoff_measurable_semigroup_patched_of_not_mem _ _ _ _ h]
      exact MarkovProcess.isFellerKernelSemigroup_idSemigroup
  · filter_upwards [hGae] with omega homega N
    exact aux_finiteDimensional_cutoff_measurable_semigroup_patched_of_mem _ _ _ _ homega

end SubdiffusiveProcess.Paper
