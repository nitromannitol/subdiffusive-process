module

public import Mathlib
public import SubdiffusiveProcess.Probability.JointLawLimits

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology InnerProductSpace

noncomputable section
namespace Paper

/-- A norm limit of symmetric bounded operators is symmetric. -/
theorem aux_conv_represented_limit_identification_symm_of_tendsto
    {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
    (G : ℕ → 𝓗 →L[ℝ] 𝓗) (L : 𝓗 →L[ℝ] 𝓗)
    (hsym : ∀ n x y, ⟪G n x, y⟫_ℝ = ⟪x, G n y⟫_ℝ) (hG : Tendsto G atTop (𝓝 L)) :
    ∀ x y, ⟪L x, y⟫_ℝ = ⟪x, L y⟫_ℝ := by
  intro x y
  have happ : ∀ w, Tendsto (fun n => G n w) atTop (𝓝 (L w)) := fun w =>
    ((ContinuousLinearMap.apply ℝ 𝓗 w).continuous.tendsto L).comp hG
  have h1 : Tendsto (fun n => ⟪G n x, y⟫_ℝ) atTop (𝓝 ⟪L x, y⟫_ℝ) :=
    (happ x).inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪x, G n y⟫_ℝ) atTop (𝓝 ⟪x, L y⟫_ℝ) :=
    tendsto_const_nhds.inner (happ y)
  exact tendsto_nhds_unique h1 (by simpa only [hsym] using h2)

/-- Two symmetric bounded operators with equal quadratic tests on a dense set closed under
addition are equal. -/
theorem aux_conv_represented_limit_identification_eq_of_tests
    {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
    (S₁ S₂ : 𝓗 →L[ℝ] 𝓗)
    (h₁ : ∀ x y, ⟪S₁ x, y⟫_ℝ = ⟪x, S₁ y⟫_ℝ) (h₂ : ∀ x y, ⟪S₂ x, y⟫_ℝ = ⟪x, S₂ y⟫_ℝ)
    (D : Set 𝓗) (hD : Dense D) (hDadd : ∀ a ∈ D, ∀ b ∈ D, a + b ∈ D)
    (h : ∀ x ∈ D, ⟪x, S₁ x⟫_ℝ = ⟪x, S₂ x⟫_ℝ) : S₁ = S₂ := by
  have hcross : ∀ a ∈ D, ∀ b ∈ D, ⟪a, S₁ b⟫_ℝ = ⟪a, S₂ b⟫_ℝ := by
    intro a ha b hb
    have hpol : ∀ S : 𝓗 →L[ℝ] 𝓗, (∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ) →
        2 * ⟪a, S b⟫_ℝ = ⟪a + b, S (a + b)⟫_ℝ - ⟪a, S a⟫_ℝ - ⟪b, S b⟫_ℝ := by
      intro S hS
      have hba : ⟪b, S a⟫_ℝ = ⟪a, S b⟫_ℝ := by
        rw [real_inner_comm, hS a b, real_inner_comm]
      simp only [map_add, inner_add_left, inner_add_right]
      linarith
    have e1 := hpol S₁ h₁
    have e2 := hpol S₂ h₂
    rw [h (a + b) (hDadd a ha b hb), h a ha, h b hb] at e1
    linarith
  have hall : ∀ a b : 𝓗, ⟪a, S₁ b⟫_ℝ = ⟪a, S₂ b⟫_ℝ := by
    have hclosed : IsClosed {p : 𝓗 × 𝓗 | ⟪p.1, S₁ p.2⟫_ℝ = ⟪p.1, S₂ p.2⟫_ℝ} :=
      isClosed_eq (continuous_fst.inner (S₁.continuous.comp continuous_snd))
        (continuous_fst.inner (S₂.continuous.comp continuous_snd))
    have hDD : Dense (D ×ˢ D) := hD.prod hD
    have hsub : D ×ˢ D ⊆ {p : 𝓗 × 𝓗 | ⟪p.1, S₁ p.2⟫_ℝ = ⟪p.1, S₂ p.2⟫_ℝ} :=
      fun p hp => hcross p.1 hp.1 p.2 hp.2
    have hsuper : (univ : Set (𝓗 × 𝓗)) ⊆
        {p : 𝓗 × 𝓗 | ⟪p.1, S₁ p.2⟫_ℝ = ⟪p.1, S₂ p.2⟫_ℝ} := by
      have := closure_minimal hsub hclosed
      rwa [hDD.closure_eq] at this
    intro a b
    exact hsuper (mem_univ (a, b))
  ext b
  exact ext_inner_left ℝ fun a => hall a b


/-- **Identification of the represented limit.**  Let the operators `T n β` be functions of the
environment `β`, with measurable quadratic tests on a countable dense additive test set `D`, and
let `T n β → L0 β` in norm for almost every `β`.  On a probability space carrying environments
`env n` and `envLim` of the original law along which `T (seq n) (env n ·)` converges in norm to
`Lh`, the represented limit is the original limit evaluated at the limiting environment:
`Lh ω = L0 (envLim ω)` almost surely.  Only the law of the vector `(env n, T (seq n) (env n))` at
each fixed `n` is used (it is the image of the original law under a measurable graph map), so no
cross-index law is assumed. -/
theorem conv_represented_limit_identification
    {E : Type} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
    (P0 : Measure E) [IsProbabilityMeasure P0]
    {Ωh : Type*} [MeasurableSpace Ωh] (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
    (T : ℕ → E → 𝓗 →L[ℝ] 𝓗) (L0 : E → 𝓗 →L[ℝ] 𝓗) (Lh : Ωh → 𝓗 →L[ℝ] 𝓗)
    (seq : ℕ → ℕ) (hseq : StrictMono seq)
    (env : ℕ → Ωh → E) (envLim : Ωh → E)
    (hsym : ∀ n β x y, ⟪T n β x, y⟫_ℝ = ⟪x, T n β y⟫_ℝ)
    (D : Set 𝓗) (hDcount : D.Countable) (hDdense : Dense D)
    (hDadd : ∀ a ∈ D, ∀ b ∈ D, a + b ∈ D)
    (hmeas : ∀ n, ∀ x ∈ D, Measurable (fun β => ⟪x, T n β x⟫_ℝ))
    (hmp : ∀ n, MeasurePreserving (env n) Ph P0) (hmpLim : MeasurePreserving envLim Ph P0)
    (horig : ∀ᵐ β ∂P0, Tendsto (fun n => T n β) atTop (𝓝 (L0 β)))
    (hrep : ∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (envLim ω)) ∧
      Tendsto (fun n => T (seq n) (env n ω)) atTop (𝓝 (Lh ω))) :
    ∀ᵐ ω ∂Ph, Lh ω = L0 (envLim ω) := by
  classical
  have hcont : ∀ x : 𝓗, Continuous (fun A : 𝓗 →L[ℝ] 𝓗 => ⟪x, A x⟫_ℝ) := fun x =>
    continuous_const.inner ((ContinuousLinearMap.apply ℝ 𝓗 x).continuous)
  -- quadratic tests agree at the limiting environment, for each fixed test vector
  have htest : ∀ x ∈ D, ∀ᵐ ω ∂Ph, ⟪x, Lh ω x⟫_ℝ = ⟪x, L0 (envLim ω) x⟫_ℝ := by
    intro x hx
    let X : ℕ → E → ℝ := fun n β => ⟪x, T (seq n) β x⟫_ℝ
    have hXm : ∀ n, Measurable (X n) := fun n => hmeas (seq n) x hx
    have hXlim : ∀ᵐ β ∂P0, Tendsto (fun n => X n β) atTop
        (𝓝 ⟪x, L0 β x⟫_ℝ) := by
      filter_upwards [horig] with β hβ
      exact ((hcont x).tendsto _).comp (hβ.comp hseq.tendsto_atTop)
    have hmk : AEMeasurable (fun β => ⟪x, L0 β x⟫_ℝ) P0 :=
      aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hXm n).aemeasurable) hXlim
    set q : E → ℝ := hmk.mk _ with hq
    have hqm : Measurable q := hmk.measurable_mk
    have hqae : ∀ᵐ β ∂P0, ⟪x, L0 β x⟫_ℝ = q β := hmk.ae_eq_mk
    let Yn : ℕ → Ωh → ℝ := fun n ω => X n (env n ω)
    have hYm : ∀ n, Measurable (Yn n) := fun n => (hXm n).comp (hmp n).measurable
    have hYlim : ∀ᵐ ω ∂Ph, Tendsto (fun n => Yn n ω) atTop (𝓝 ⟪x, Lh ω x⟫_ℝ) := by
      filter_upwards [hrep] with ω hω
      exact ((hcont x).tendsto _).comp hω.2
    have hmkY : AEMeasurable (fun ω => ⟪x, Lh ω x⟫_ℝ) Ph :=
      aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hYm n).aemeasurable) hYlim
    set qY : Ωh → ℝ := hmkY.mk _ with hqY
    have hqYm : Measurable qY := hmkY.measurable_mk
    have hqYae : ∀ᵐ ω ∂Ph, ⟪x, Lh ω x⟫_ℝ = qY ω := hmkY.ae_eq_mk
    have hlaw : ∀ n, Measure.map (fun ω => (env n ω, Yn n ω)) Ph =
        Measure.map (fun β => (β, X n β)) P0 := by
      intro n
      have hgraph : Measurable (fun β : E => (β, X n β)) := measurable_id.prodMk (hXm n)
      have : (fun ω => (env n ω, Yn n ω)) = (fun β : E => (β, X n β)) ∘ env n := rfl
      rw [this, ← Measure.map_map hgraph (hmp n).measurable, (hmp n).map_eq]
    have hconv : ∀ᵐ β ∂P0, Tendsto (fun n => X n β) atTop (𝓝 (q β)) := by
      filter_upwards [hXlim, hqae] with β h1 h2
      rwa [← h2]
    have hconvHat : ∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (envLim ω)) ∧
        Tendsto (fun n => Yn n ω) atTop (𝓝 (qY ω)) := by
      filter_upwards [hrep, hYlim, hqYae] with ω h1 h2 h3
      exact ⟨h1.1, by rwa [← h3]⟩
    have hid := SubdiffusiveProcess.Probability.ae_eq_of_joint_map_eq_of_ae_tendsto P0 Ph
      X q env envLim Yn qY hXm hqm (fun n => (hmp n).measurable) hmpLim.measurable hYm hqYm
      (fun n => by simpa [Function.comp_def] using hlaw n) hconv hconvHat
    have hqae' : ∀ᵐ ω ∂Ph, ⟪x, L0 (envLim ω) x⟫_ℝ = q (envLim ω) :=
      hmpLim.quasiMeasurePreserving.ae hqae
    filter_upwards [hqYae, hid, hqae'] with ω h1 h2 h3
    rw [h1, h2, h3]
  have hall : ∀ᵐ ω ∂Ph, ∀ x ∈ D, ⟪x, Lh ω x⟫_ℝ = ⟪x, L0 (envLim ω) x⟫_ℝ :=
    (MeasureTheory.ae_ball_iff hDcount).2 htest
  have horigLim : ∀ᵐ ω ∂Ph, Tendsto (fun n => T n (envLim ω)) atTop (𝓝 (L0 (envLim ω))) :=
    hmpLim.quasiMeasurePreserving.ae horig
  filter_upwards [hall, horigLim, hrep] with ω h1 h2 h3
  exact aux_conv_represented_limit_identification_eq_of_tests _ _
    (aux_conv_represented_limit_identification_symm_of_tendsto
      (fun n => T (seq n) (env n ω)) (Lh ω) (fun n x y => hsym _ _ x y) h3.2)
    (aux_conv_represented_limit_identification_symm_of_tendsto
      (fun n => T n (envLim ω)) (L0 (envLim ω)) (fun n x y => hsym _ _ x y) h2)
    D hDdense hDadd h1

end Paper
