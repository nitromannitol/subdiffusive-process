module

public import SubdiffusiveProcess.DirichletForm.EnergyMeasureLowerSemicontinuity
public import SubdiffusiveProcess.Sobolev.ContinuousTraceLimit

@[expose] public section

/-! Bounded-energy limits preserve continuous trace-response witnesses.
This module provides the closure step once approximating domain elements and
their uniform limits are constructed; it does not construct those approximants.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section
namespace SubdiffusiveProcess.DirichletForm.EnergyMeasure

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable {mu : Measure X} {E : ClosedForm mu}

/-- Energy values of continuous domain representatives with a prescribed local trace. -/
def continuousTraceValues (Gamma : EnergyMeasure E) (S B : Set X) (b : X → ℝ) : Set ℝ :=
  {e : ℝ | ∃ (v : Lp ℝ 2 mu) (V : X → ℝ),
    v ∈ E.domain ∧ ContinuousOn V S ∧ (v : X → ℝ) =ᵐ[mu] V ∧
    (∀ x ∈ frontier B, V x = b x) ∧ e = (Gamma.measure v B).toReal}

/-- A bounded-energy L2 limit and a uniform trace limit give a local response witness. -/
theorem continuousTraceValues_of_tendsto
    (Gamma : EnergyMeasure E) (S B : Set X) (hB : MeasurableSet B)
    (hBS : frontier B ⊆ S) (hS : ∀ᵐ x ∂mu, x ∈ S)
    (un : ℕ → Lp ℝ 2 mu) (hu : ∀ n, un n ∈ E.domain)
    (u : Lp ℝ 2 mu) (hL2 : Tendsto un atTop (𝓝 u))
    (VN bN : ℕ → X → ℝ) (V b : X → ℝ)
    (hVN : ∀ n, ContinuousOn (VN n) S)
    (hrep : ∀ n, (un n : X → ℝ) =ᵐ[mu] VN n)
    (hVlim : TendstoUniformlyOn VN V atTop S)
    (hblim : TendstoUniformlyOn bN b atTop (frontier B))
    (htrace : ∀ n, EqOn (VN n) (bN n) (frontier B))
    (E0 K : ℝ) (hE0 : ∀ n, E.form (un n) (un n) ≤ E0)
    (hK : ∀ n, (Gamma.measure (un n) B).toReal ≤ K) :
    (Gamma.continuousTraceValues S B b).Nonempty ∧
      IsGLB (Gamma.continuousTraceValues S B b)
        (sInf (Gamma.continuousTraceValues S B b)) ∧
      sInf (Gamma.continuousTraceValues S B b) ≤ K := by
  obtain ⟨hu', hlocal⟩ := local_bound_of_tendsto_of_form_le
    E Gamma un hu u hL2 E0 K hE0 B hB hK
  have hVc : ContinuousOn V S := hVlim.continuousOn
    (Eventually.of_forall hVN).frequently
  have hVr := SubdiffusiveProcess.ae_eq_of_tendsto_Lp_of_tendstoUniformlyOn
    S hS un u hL2 VN V hrep hVlim
  have hVb := SubdiffusiveProcess.eqOn_of_uniform_limits_of_eqOn
    S (frontier B) hBS VN bN V b hVlim hblim htrace
  have hmem : (Gamma.measure u B).toReal ∈ Gamma.continuousTraceValues S B b :=
    ⟨u, V, hu', hVc, hVr, fun x hx => hVb hx, rfl⟩
  have hbelow : BddBelow (Gamma.continuousTraceValues S B b) := by
    refine ⟨0, ?_⟩
    rintro e ⟨v, W, hv, hWc, hWr, hWt, rfl⟩
    exact ENNReal.toReal_nonneg
  exact ⟨⟨_, hmem⟩, isGLB_csInf ⟨_, hmem⟩ hbelow, (csInf_le hbelow hmem).trans hlocal⟩

end SubdiffusiveProcess.DirichletForm.EnergyMeasure
