module

public import SubdiffusiveProcess.DirichletForm.ContinuousTraceResponse
public import SubdiffusiveProcess.Sobolev.GoodCellEnergyScaling

@[expose] public section

/-!
# Good-cell trace response

This module combines a continuous trace witness with the scalar reference-ratio
estimate; it does not construct the witness or establish its analytic bounds.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal
noncomputable section
namespace SubdiffusiveProcess.DirichletForm.EnergyMeasure

/-- A continuous trace witness controls the infimal response by the reference-ratio bound. -/
theorem continuousTraceValues_le_reference_ratio
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {mu : Measure X} {E : ClosedForm mu} (Gamma : EnergyMeasure E)
    (S B : Set X) (b : X → ℝ) (d : ℕ)
    (trace C Ce r se sf nu f : ℝ)
    (htrace : 0 ≤ trace) (hC : 0 ≤ C) (hCe : 0 ≤ Ce)
    (hr : 0 < r) (hse : 0 < se) (hsf : 0 ≤ sf)
    (hnu : 0 ≤ nu) (hf : 0 ≤ f)
    (hTrace : trace ≤ C * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) *
      Real.sqrt nu + C * r ^ (2 : ℝ) * se⁻¹ * f)
    (hWitness : ∃ (v : Lp ℝ 2 mu) (V : X → ℝ), v ∈ E.domain ∧
      ContinuousOn V S ∧ (v : X → ℝ) =ᵐ[mu] V ∧
      (∀ x ∈ frontier B, V x = b x) ∧
      (Gamma.measure v B).toReal ≤ Ce * sf * r ^ ((d : ℝ) - 2) * trace ^ 2) :
    (Gamma.continuousTraceValues S B b).Nonempty ∧
      IsGLB (Gamma.continuousTraceValues S B b)
        (sInf (Gamma.continuousTraceValues S B b)) ∧
      sInf (Gamma.continuousTraceValues S B b) ≤
        (2 * Ce * C ^ 2) * (sf / se) *
          (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * f ^ 2) := by
  obtain ⟨v, V, hv, hVc, hrep, hBoundary, hEnergy⟩ := hWitness

  have hmem : (Gamma.measure v B).toReal ∈ Gamma.continuousTraceValues S B b :=
    ⟨v, V, hv, hVc, hrep, hBoundary, rfl⟩

  have hnonneg : ∀ e ∈ Gamma.continuousTraceValues S B b, 0 ≤ e := by
    intro e he
    rcases he with ⟨v', V', hv', hV'c, hrep', hBoundary', rfl⟩
    exact ENNReal.toReal_nonneg

  have hbelow : BddBelow (Gamma.continuousTraceValues S B b) :=
    ⟨0, hnonneg⟩
  have hnonempty : (Gamma.continuousTraceValues S B b).Nonempty := ⟨_, hmem⟩
  have hglb : IsGLB (Gamma.continuousTraceValues S B b)
      (sInf (Gamma.continuousTraceValues S B b)) :=
    isGLB_csInf hnonempty hbelow

  have hlocal : (Gamma.measure v B).toReal ≤
      (2 * Ce * C ^ 2) * (sf / se) *
        (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * f ^ 2) := by
    exact SubdiffusiveProcess.trace_energy_le_reference_ratio
      d trace C Ce r se sf nu f (Gamma.measure v B).toReal
      htrace hC hCe hr hse hsf hnu hf hTrace hEnergy

  exact ⟨hnonempty, hglb, (csInf_le hbelow hmem).trans hlocal⟩
