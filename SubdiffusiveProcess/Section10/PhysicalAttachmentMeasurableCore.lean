module

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
public import SubdiffusiveProcess.Main.DiffusionPath
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalAttachment

/- Generic proofs extracted from the existing finiteDimensional_cutoff_measurable_semigroup. -/
section aux_hilleYosida

open Filter MeasureTheory Topology
open scoped NNReal

open MarkovProcess MarkovProcess.Semigroup

/-- Joint measurability of a measurable family of continuous linear maps, evaluated along a
measurable vector field. -/
theorem pa_measurable_clm_comp
    {Θ E : Type*} [MeasurableSpace Θ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (A : Θ → E →L[ℝ] E) (hA : ∀ y, Measurable fun θ ↦ A θ y)
    {g : Θ → E} (hg : Measurable g) :
    Measurable fun θ ↦ A θ (g θ) := by
  have hjoint : Measurable (Function.uncurry fun (y : E) (θ : Θ) ↦ A θ y) :=
    measurable_uncurry_of_continuous_of_measurable (fun θ ↦ (A θ).continuous) hA
  exact hjoint.comp (hg.prodMk measurable_id)

/-- Iterates of a measurable family of continuous linear maps are measurable. -/
theorem pa_measurable_clm_iterate
    {Θ E : Type*} [MeasurableSpace Θ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (A : Θ → E →L[ℝ] E) (hA : ∀ y, Measurable fun θ ↦ A θ y) (n : ℕ) (y : E) :
    Measurable fun θ ↦ (A θ)^[n] y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact pa_measurable_clm_comp A hA ih

/-- The exponential of a measurable family of continuous linear maps acts measurably. -/
theorem pa_measurable_exp
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
    exact (pa_measurable_clm_iterate
      A hA n y).const_smul _
  · exact tendsto_pi_nhds.2 fun θ ↦ (hsum θ).tendsto_sum_nat

/-- **Parametric Hille--Yosida measurability.** If every resolvent operator of a family of
contractive resolvents is measurable in the parameter, so is every orbit of the generated
semigroup. -/
theorem pa_measurable_generated
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
    simp only [ContractiveResolvent.yosidaGenerator, ContractiveResolvent.scaledOperator, smul_apply, sub_apply, ContinuousLinearMap.id_apply]
  have hyos : ∀ n : ℕ, Measurable fun θ ↦
      (R θ).yosidaOperator (naturalShift n) t y := by
    intro n
    exact pa_measurable_exp
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
def pa_cutoff (d n : ℕ) :
    C(Fin d → ℝ, ℝ) :=
  ⟨fun x ↦ max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)), by fun_prop⟩

theorem pa_cutoff_apply (d n : ℕ)
    (x : Fin d → ℝ) :
    pa_cutoff d n x =
      max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)) := rfl

/-- A continuous function cut off radially, as an element of `C₀`. -/
def pa_cutoffMul (d n : ℕ)
    (q : C(Fin d → ℝ, ℝ)) : C₀(Fin d → ℝ, ℝ) where
  toFun x := pa_cutoff d n x * q x
  continuous_toFun := by fun_prop
  zero_at_infty' := by
    have hcs : HasCompactSupport (fun x ↦
        pa_cutoff d n x * q x) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℝ) ((n : ℝ) + 1)) ?_
      intro x hx
      have hx' : (n : ℝ) + 1 < ‖x‖ := by
        simpa [mem_closedBall, dist_zero_right, not_le] using hx
      have hzero : pa_cutoff d n x = 0 := by
        rw [pa_cutoff_apply]
        have h1 : min 1 ((n : ℝ) + 1 - ‖x‖) ≤ 0 := (min_le_right _ _).trans (by linarith)
        exact max_eq_left h1
      simp [hzero]
    exact hcs.is_zero_at_infty

theorem pa_cutoffMul_apply (d n : ℕ)
    (q : C(Fin d → ℝ, ℝ)) (x : Fin d → ℝ) :
    pa_cutoffMul d n q x =
      pa_cutoff d n x * q x := rfl

/-- Functions vanishing at infinity on `ℝᵈ` form a separable space. -/
theorem pa_c0_separable (d : ℕ) :
    TopologicalSpace.SeparableSpace C₀(Fin d → ℝ, ℝ) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense C(Fin d → ℝ, ℝ)
  let S : Set C₀(Fin d → ℝ, ℝ) :=
    ⋃ n : ℕ, (pa_cutoffMul d n) '' D
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
  refine ⟨pa_cutoffMul d n q, ?_,
    Set.mem_iUnion.2 ⟨n, Set.mem_image_of_mem _ hqD⟩⟩
  rw [Metric.mem_ball, dist_comm]
  rw [dist_eq_norm, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine (BoundedContinuousFunction.norm_le (by linarith)).2 fun x ↦ ?_
  change ‖f x - pa_cutoffMul d n q x‖ ≤ ε / 2
  rw [pa_cutoffMul_apply,
    pa_cutoff_apply, Real.norm_eq_abs]
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

theorem pa_c0_secondCountable (d : ℕ) :
    SecondCountableTopology C₀(Fin d → ℝ, ℝ) := by
  have := pa_c0_separable d
  exact UniformSpace.secondCountable_of_separable _

theorem pa_c0_polish (d : ℕ) :
    PolishSpace C₀(Fin d → ℝ, ℝ) := by
  have := pa_c0_separable d
  infer_instance

end aux_c0Separable

section aux_souslin

open Filter MeasureTheory Topology Set

/-- **Measurability from a uniquely solvable analytic relation.** Let `A ⊆ P × Y` be analytic
in a Polish product and single-valued over every parameter. If a map `s` is a section of `A`
over a measurable parameter map on a set `G`, then `s` is measurable on `G`: the two
projections of `A` over an open set and over its complement are disjoint analytic sets, and a
Lusin separating Borel set describes the preimage. -/
theorem pa_measurable_of_analytic
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
    simpa using this
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
theorem pa_eventually_unif
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
theorem pa_c0_apply_le
    {X : Type*} [TopologicalSpace X] (g : C₀(X, ℝ)) (x : X) : |g x| ≤ ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, ← Real.norm_eq_abs]
  exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF x

/-- Evaluation of a function vanishing at infinity is continuous in the function. -/
theorem pa_c0_continuous_eval
    {X : Type*} [TopologicalSpace X] (x : X) :
    Continuous fun g : C₀(X, ℝ) ↦ g x := by
  have h : Continuous fun g : BoundedContinuousFunction X ℝ ↦ g x := continuous_eval_const x
  exact h.comp ZeroAtInftyContinuousMap.isometry_toBCF.continuous

/-- **Continuity of the weighted mass pairing.** On a bounded measurable set, the pairing
`(ρ, g) ↦ ∫_U ρ g ψ` is continuous for `ψ` integrable on `U`, with `ρ` locally uniform and
`g` in the `C₀` norm. -/
theorem pa_continuous_mass
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
      (pa_eventually_unif hK ρ₀ one_pos)
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
      have h1 := pa_c0_apply_le q.2 x
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
      (pa_c0_continuous_eval x).comp
        continuous_snd
    exact ((h1.mul h2).mul continuous_const).continuousAt

/-- A continuous multiplier of an `L²(U)` function on a bounded set, as an `L²` element. -/
def pa_mulLp
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

theorem pa_mulLp_ae
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) (c : C(Fin d → ℝ, ℝ)) :
    (pa_mulLp hU hUb hψ c :
        (Fin d → ℝ) → ℝ) =ᵐ[volume.restrict U] fun x ↦ c x * ψ x :=
  MemLp.coeFn_toLp _

/-- The continuous multiplier map into `L²(U)` is continuous for locally uniform convergence. -/
theorem pa_continuous_mulLp
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) :
    Continuous (pa_mulLp hU hUb hψ) := by
  rw [continuous_iff_continuousAt]
  intro c₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set L : ℝ := (eLpNorm ψ 2 (volume.restrict U)).toReal with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (2 * (L + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  filter_upwards [pa_eventually_unif
    hUb.isCompact_closure c₀ hδ0] with c hc
  rw [Lp.dist_edist, pa_mulLp,
    pa_mulLp, Lp.edist_toLp_toLp]
  have hbound : eLpNorm ((fun x ↦ c x * ψ x) - fun x ↦ c₀ x * ψ x) 2 (volume.restrict U) ≤
      eLpNorm (δ • ψ) 2 (volume.restrict U) := by
    refine eLpNorm_mono_ae ((c.continuous.aestronglyMeasurable.mul hψ.aestronglyMeasurable).sub (c₀.continuous.aestronglyMeasurable.mul hψ.aestronglyMeasurable)) ?_
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
theorem pa_integral_eq_inner
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) (c : C(Fin d → ℝ, ℝ))
    (G : Lp ℝ 2 (volume.restrict U)) :
    ∫ x in U, c x * (G : (Fin d → ℝ) → ℝ) x * ψ x =
      inner ℝ G (pa_mulLp hU hUb hψ c) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [pa_mulLp_ae hU hUb hψ c]
    with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **Continuity of the weighted gradient pairing** in the coefficient (locally uniformly) and
the gradient component (in `L²(U)`). -/
theorem pa_continuous_grad
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) :
    Continuous fun q : C(Fin d → ℝ, ℝ) × Lp ℝ 2 (volume.restrict U) ↦
      ∫ x in U, q.1 x * (q.2 : (Fin d → ℝ) → ℝ) x * ψ x := by
  have h : Continuous fun q : C(Fin d → ℝ, ℝ) × Lp ℝ 2 (volume.restrict U) ↦
      inner ℝ q.2 (pa_mulLp hU hUb hψ q.1) :=
    continuous_snd.inner
      ((pa_continuous_mulLp hU hUb hψ).comp
        continuous_fst)
  refine h.congr fun q ↦ ?_
  exact (pa_integral_eq_inner
    hU hUb hψ q.1 q.2).symm

end aux_continuity
end SubdiffusiveProcess.Section10.PhysicalAttachment
