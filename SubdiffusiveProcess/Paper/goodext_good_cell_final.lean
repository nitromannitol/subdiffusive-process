module

public import SubdiffusiveProcess.Sobolev.GoodCellTraceAssembly
public import SubdiffusiveProcess.Lane3.Interfaces

@[expose] public section

/-! Final good-cell assembly of `lem_goodext` from calibrated constants and the three good-cell inputs; no probabilistic claim. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Final good-cell assembly of `lem_goodext`: the calibrated constants, the sourced Hölder
bound, the parent oscillation and the local trace extension give both good-cell displays. -/
theorem goodext_good_cell_final
    {d : ℕ} {mu : Measure (SpatialCoordinates d)} {E : DirichletForm.ClosedForm mu}
    (Gamma : DirichletForm.EnergyMeasure E) (S : Set (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r alpha beta se sf nu fsup osc e0 e1 : ℝ)
    (Cbase Kp tau t CeTrace Ctotal : ℝ)
    (hr : 0 < r) (hba : beta ≤ alpha) (hb : 0 < beta) (hse : 0 < se) (hsf : 0 ≤ sf)
    (hnu : 0 ≤ nu) (hf : 0 ≤ fsup) (hCbase : 0 < Cbase) (hKp : 0 ≤ Kp) (hCe : 0 ≤ CeTrace)
    (hCost : Cbase * (Kp * Real.exp (tau / 2) + 1) * (3 : ℝ) ^ (Cbase * t) ≤ Ctotal ∧
      2 * CeTrace * ((Real.sqrt d) ^ (alpha - beta) *
        (Cbase * (Kp * Real.exp (tau / 2) + 1) * (3 : ℝ) ^ (Cbase * t))) ^ 2 ≤ Ctotal)
    (U : SpatialCoordinates d → ℝ)
    (hUc : ContinuousOn U (frontier (Metric.ball z (r / 2))))
    (hSource : ∃ cq : ℝ,
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ≤
        Cbase * (3 : ℝ) ^ (Cbase * t) * (osc + r ^ (2 : ℝ) * se⁻¹ * fsup))
    (hOsc : osc ≤ Kp * Real.exp (tau / 2) * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) *
      Real.sqrt nu)
    (hExtension : IsHolderOn beta (frontier (Metric.ball z (r / 2))) U →
      ∃ (v : MeasureTheory.Lp ℝ 2 mu) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧ ContinuousOn V S ∧ (v : SpatialCoordinates d → ℝ) =ᵐ[mu] V ∧
        (∀ x ∈ frontier (Metric.ball z (r / 2)), V x = U x) ∧
        (Gamma.measure v (Metric.ball z (r / 2))).toReal ≤
          CeTrace * sf * r ^ ((d : ℝ) - 2) *
            (r ^ beta * holderSeminorm beta (frontier (Metric.ball z (r / 2))) U) ^ 2)
    (hRatio : sf / se = e1 / e0) :
    ∃ cq : ℝ,
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ≤
        Ctotal * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu +
          Ctotal * r ^ (2 : ℝ) * se⁻¹ * fsup ∧
      (Gamma.continuousTraceValues S (Metric.ball z (r / 2)) U).Nonempty ∧
      IsGLB (Gamma.continuousTraceValues S (Metric.ball z (r / 2)) U)
        (sInf (Gamma.continuousTraceValues S (Metric.ball z (r / 2)) U)) ∧
      sInf (Gamma.continuousTraceValues S (Metric.ball z (r / 2)) U) ≤
        Ctotal * (e1 / e0) * (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2) := by
  have hCs : 0 ≤ Cbase * (3 : ℝ) ^ (Cbase * t) :=
    mul_nonneg hCbase.le (Real.rpow_nonneg (by norm_num) _)
  have hCo : 0 ≤ Kp * Real.exp (tau / 2) := mul_nonneg hKp (Real.exp_pos _).le
  have hLinear : Cbase * (3 : ℝ) ^ (Cbase * t) * (Kp * Real.exp (tau / 2) + 1) ≤ Ctotal := by
    calc Cbase * (3 : ℝ) ^ (Cbase * t) * (Kp * Real.exp (tau / 2) + 1)
        = Cbase * (Kp * Real.exp (tau / 2) + 1) * (3 : ℝ) ^ (Cbase * t) := by ring
      _ ≤ Ctotal := hCost.1
  have hQuadratic : 2 * CeTrace * ((Real.sqrt d) ^ (alpha - beta) *
      (Cbase * (3 : ℝ) ^ (Cbase * t) * (Kp * Real.exp (tau / 2) + 1))) ^ 2 ≤ Ctotal := by
    calc 2 * CeTrace * ((Real.sqrt d) ^ (alpha - beta) *
          (Cbase * (3 : ℝ) ^ (Cbase * t) * (Kp * Real.exp (tau / 2) + 1))) ^ 2
        = 2 * CeTrace * ((Real.sqrt d) ^ (alpha - beta) *
          (Cbase * (Kp * Real.exp (tau / 2) + 1) * (3 : ℝ) ^ (Cbase * t))) ^ 2 := by ring
      _ ≤ Ctotal := hCost.2
  obtain ⟨cq', hHolder', hNorm', hNonempty', hGLB', hResponse'⟩ :=
    good_cell_trace_response_of_source_bound Gamma S z r alpha beta se sf nu fsup osc
      (Cbase * (3 : ℝ) ^ (Cbase * t)) (Kp * Real.exp (tau / 2)) CeTrace Ctotal hr hba hb hse hsf
      hnu hf hCs hCo hCe hLinear hQuadratic U hUc hSource hOsc hExtension
  rw [hRatio] at hResponse'
  exact ⟨cq', hHolder', hNorm', hNonempty', hGLB', hResponse'⟩


end Paper
