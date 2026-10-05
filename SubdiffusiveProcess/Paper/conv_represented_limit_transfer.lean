module

public import Mathlib
public import SubdiffusiveProcess.Paper.conv_represented_limit_identification

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology InnerProductSpace

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Quadratic tests of an almost-sure norm limit of measurable tests are almost surely equal to a
measurable function. -/
theorem aux_conv_represented_limit_transfer_test_mk
    {E : Type} [MeasurableSpace E] {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
    (P0 : Measure E) (T : ℕ → E → 𝓗 →L[ℝ] 𝓗) (L0 : E → 𝓗 →L[ℝ] 𝓗) (x : 𝓗)
    (hmeas : ∀ n, Measurable (fun β => ⟪x, T n β x⟫_ℝ))
    (horig : ∀ᵐ β ∂P0, Tendsto (fun n => T n β) atTop (𝓝 (L0 β))) :
    ∃ q : E → ℝ, Measurable q ∧ ∀ᵐ β ∂P0, ⟪x, L0 β x⟫_ℝ = q β := by
  have hcont : Continuous (fun A : 𝓗 →L[ℝ] 𝓗 => ⟪x, A x⟫_ℝ) :=
    continuous_const.inner ((ContinuousLinearMap.apply ℝ 𝓗 x).continuous)
  have hlim : ∀ᵐ β ∂P0, Tendsto (fun n => ⟪x, T n β x⟫_ℝ) atTop (𝓝 ⟪x, L0 β x⟫_ℝ) := by
    filter_upwards [horig] with β hβ
    exact (hcont.tendsto _).comp hβ
  have hmk : AEMeasurable (fun β => ⟪x, L0 β x⟫_ℝ) P0 :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hmeas n).aemeasurable) hlim
  exact ⟨hmk.mk _, hmk.measurable_mk, hmk.ae_eq_mk⟩

/-- **Transfer of an equality of limits from the represented space to the original space.**
If two subsequential limits `L0 true`, `L0 false` of environment-dependent operators are
identified with represented limits `Lh true`, `Lh false` (by
`conv_represented_limit_identification`), and the represented limits agree almost surely, then
the original limits agree almost surely. Null-measurability of the equality event is obtained
from the countable family of measurable quadratic tests; no measurability of the operator-valued
limit in the operator norm is used. -/
theorem conv_represented_limit_transfer
    {E : Type} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
    (P0 : Measure E) [IsProbabilityMeasure P0]
    {Ωh : Type*} [MeasurableSpace Ωh] (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
    (T : Bool → ℕ → E → 𝓗 →L[ℝ] 𝓗) (L0 : Bool → E → 𝓗 →L[ℝ] 𝓗)
    (Lh : Bool → Ωh → 𝓗 →L[ℝ] 𝓗)
    (seq : ℕ → ℕ) (hseq : StrictMono seq)
    (env : ℕ → Ωh → E) (envLim : Ωh → E)
    (hsym : ∀ b n β x y, ⟪T b n β x, y⟫_ℝ = ⟪x, T b n β y⟫_ℝ)
    (D : Set 𝓗) (hDcount : D.Countable) (hDdense : Dense D)
    (hDadd : ∀ a ∈ D, ∀ b ∈ D, a + b ∈ D)
    (hmeas : ∀ b n, ∀ x ∈ D, Measurable (fun β => ⟪x, T b n β x⟫_ℝ))
    (hmp : ∀ n, MeasurePreserving (env n) Ph P0) (hmpLim : MeasurePreserving envLim Ph P0)
    (horig : ∀ b, ∀ᵐ β ∂P0, Tendsto (fun n => T b n β) atTop (𝓝 (L0 b β)))
    (hrep : ∀ b, ∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (envLim ω)) ∧
      Tendsto (fun n => T b (seq n) (env n ω)) atTop (𝓝 (Lh b ω)))
    (hEF : ∀ᵐ ω ∂Ph, Lh true ω = Lh false ω) :
    ∀ᵐ β ∂P0, L0 true β = L0 false β := by
  classical
  have hid : ∀ b, ∀ᵐ ω ∂Ph, Lh b ω = L0 b (envLim ω) := fun b =>
    conv_represented_limit_identification P0 Ph (T b) (L0 b) (Lh b) seq hseq env envLim
      (hsym b) D hDcount hDdense hDadd (hmeas b) hmp hmpLim (horig b) (hrep b)
  have hEFlim : ∀ᵐ ω ∂Ph, L0 true (envLim ω) = L0 false (envLim ω) := by
    filter_upwards [hEF, hid true, hid false] with ω h1 h2 h3
    rw [← h2, ← h3, h1]
  -- measurable descriptions of the tests
  have hmk : ∀ b, ∀ x ∈ D, ∃ q : E → ℝ, Measurable q ∧ ∀ᵐ β ∂P0, ⟪x, L0 b β x⟫_ℝ = q β :=
    fun b x hx => aux_conv_represented_limit_transfer_test_mk P0 (T b) (L0 b) x
      (fun n => hmeas b n x hx) (horig b)
  choose! q hqm hqae using hmk
  have hsymLim : ∀ b, ∀ᵐ β ∂P0, ∀ x y, ⟪L0 b β x, y⟫_ℝ = ⟪x, L0 b β y⟫_ℝ := by
    intro b
    filter_upwards [horig b] with β hβ
    exact aux_conv_represented_limit_identification_symm_of_tendsto (fun n => T b n β)
      (L0 b β) (fun n x y => hsym b n β x y) hβ
  let B : Set E := {β | ∀ x ∈ D, q true x β = q false x β}
  have hBmeas : MeasurableSet B := by
    have : B = ⋂ x ∈ D, {β | q true x β = q false x β} := by
      ext β; simp [B]
    rw [this]
    exact MeasurableSet.biInter hDcount fun x hx =>
      measurableSet_eq_fun (hqm true x hx) (hqm false x hx)
  have hae : ∀ᵐ β ∂P0, (L0 true β = L0 false β ↔ β ∈ B) := by
    have hq' : ∀ᵐ β ∂P0, ∀ b, ∀ x ∈ D, ⟪x, L0 b β x⟫_ℝ = q b x β := by
      have h1 : ∀ᵐ β ∂P0, ∀ x ∈ D, ⟪x, L0 true β x⟫_ℝ = q true x β :=
        (MeasureTheory.ae_ball_iff hDcount).2 fun x hx => hqae true x hx
      have h2 : ∀ᵐ β ∂P0, ∀ x ∈ D, ⟪x, L0 false β x⟫_ℝ = q false x β :=
        (MeasureTheory.ae_ball_iff hDcount).2 fun x hx => hqae false x hx
      filter_upwards [h1, h2] with β a b
      intro c
      cases c
      · exact b
      · exact a
    filter_upwards [hq', hsymLim true, hsymLim false] with β hq hs1 hs2
    constructor
    · intro h x hx
      rw [← hq true x hx, ← hq false x hx, h]
    · intro h
      exact aux_conv_represented_limit_identification_eq_of_tests _ _ hs1 hs2 D hDdense hDadd
        fun x hx => by rw [hq true x hx, hq false x hx]; exact h x hx
  -- pull the event back along the measure preserving limit environment
  have hnull : P0 Bᶜ = 0 := by
    have hpre : Ph (envLim ⁻¹' Bᶜ) = P0 Bᶜ := hmpLim.measure_preimage hBmeas.compl.nullMeasurableSet
    rw [← hpre]
    have hgood : ∀ᵐ ω ∂Ph, envLim ω ∈ B := by
      filter_upwards [hEFlim, hmpLim.quasiMeasurePreserving.ae hae] with ω h1 h2
      exact h2.1 h1
    exact ae_iff.1 hgood
  filter_upwards [hae, measure_eq_zero_iff_ae_notMem.1 hnull] with β h1 h2
  exact h1.2 (by simpa using h2)

end SubdiffusiveProcess.Paper
