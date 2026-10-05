module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section

/-! Uniform limits preserve continuous representatives and their prescribed traces.
The statements identify already converging functions; they assert neither
bounded energy nor existence of approximating boundary solutions.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace SubdiffusiveProcess

/-- A uniform limit of representatives represents their L2 limit. -/
theorem ae_eq_of_tendsto_Lp_of_tendstoUniformlyOn
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    (S : Set X) (hS : ∀ᵐ x ∂mu, x ∈ S)
    (un : ℕ → Lp ℝ 2 mu) (u : Lp ℝ 2 mu)
    (hL2 : Tendsto un atTop (𝓝 u))
    (VN : ℕ → X → ℝ) (V : X → ℝ)
    (hrep : ∀ n, (un n : X → ℝ) =ᵐ[mu] VN n)
    (hlim : TendstoUniformlyOn VN V atTop S) :
    (u : X → ℝ) =ᵐ[mu] V := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂mu, ∀ n, (un n : X → ℝ) x = VN n x :=
    ae_all_iff.mpr hrep
  filter_upwards [hS, hall, hae] with x hx hrepX huX
  have hVX : Tendsto (fun n => VN (ns n) x) atTop (𝓝 (V x)) :=
    (hlim.tendsto_at hx).comp hns.tendsto_atTop
  have hVX' : Tendsto (fun n => (un (ns n) : X → ℝ) x) atTop (𝓝 (V x)) :=
    hVX.congr' (Eventually.of_forall fun n => (hrepX (ns n)).symm)
  exact tendsto_nhds_unique huX hVX'

/-- Uniform convergence on a containing set preserves a uniformly converging trace. -/
theorem eqOn_of_uniform_limits_of_eqOn
    {X : Type*} (S T : Set X) (hTS : T ⊆ S)
    (VN bN : ℕ → X → ℝ) (V b : X → ℝ)
    (hV : TendstoUniformlyOn VN V atTop S)
    (hb : TendstoUniformlyOn bN b atTop T)
    (htrace : ∀ n, EqOn (VN n) (bN n) T) :
    EqOn V b T := by
  intro x hx
  have hleft := hV.tendsto_at (hTS hx)
  have hright : Tendsto (fun n => VN n x) atTop (𝓝 (b x)) :=
    (hb.tendsto_at hx).congr' (Eventually.of_forall fun n => (htrace n hx).symm)
  exact tendsto_nhds_unique hleft hright

end SubdiffusiveProcess
