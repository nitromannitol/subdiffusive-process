module

public import SubdiffusiveProcess.Sobolev.NormalizedBoundaryHolder
public import SubdiffusiveProcess.DirichletForm.GoodCellTraceResponse

@[expose] public section

/-!
# Good-cell source trace assembly

This module derives the normalized good-cell estimate and trace response from the supplied source oscillation bound and boundary extension. It does not construct either analytic input.
-/

open MeasureTheory Set _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

private theorem aux_good_cell_trace_assembly_amplitudes_nonneg
    {d : ℕ} {r se nu fsup alpha beta : ℝ}
    (hr : 0 < r) (hse : 0 < se) (hf : 0 ≤ fsup) :
    0 ≤ r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu ∧
    0 ≤ r ^ (2 : ℝ) * se⁻¹ * fsup ∧
    0 ≤ (Real.sqrt d) ^ (alpha - beta) := by
  have hrA : 0 < r ^ ((2 - (d : ℝ)) / 2) :=
    Real.rpow_pos_of_pos hr _
  have hseA : 0 < se ^ (-(1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hse _
  have hnuSqrt : 0 ≤ Real.sqrt nu := Real.sqrt_nonneg nu
  have hrB : 0 < r ^ (2 : ℝ) := Real.rpow_pos_of_pos hr _
  have hseInv : 0 ≤ se⁻¹ := inv_nonneg.mpr (le_of_lt hse)
  have hD : 0 ≤ (Real.sqrt d) ^ (alpha - beta) :=
    Real.rpow_nonneg (Real.sqrt_nonneg d) _
  exact ⟨mul_nonneg (mul_nonneg (le_of_lt hrA) (le_of_lt hseA)) hnuSqrt,
    mul_nonneg (mul_nonneg (le_of_lt hrB) hseInv) hf, hD⟩


private theorem aux_good_cell_trace_assembly_source_bound
    {A B osc Csource Cosc : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCs : 0 ≤ Csource) (hCo : 0 ≤ Cosc)
    (hOsc : osc ≤ Cosc * A) :
    Csource * (osc + B) ≤ Csource * (Cosc + 1) * A + Csource * (Cosc + 1) * B := by
  have hCoeffA : Csource * Cosc ≤ Csource * (Cosc + 1) :=
    mul_le_mul_of_nonneg_left (by linarith only []) hCs
  have hCoeffB : Csource ≤ Csource * (Cosc + 1) := by
    calc
      Csource = Csource * 1 := by ring
      _ ≤ Csource * (Cosc + 1) :=
        mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Cosc + 1 by linarith only [hCo]) hCs
  have hTermA := mul_le_mul_of_nonneg_right hCoeffA hA
  have hTermB := mul_le_mul_of_nonneg_right hCoeffB hB
  calc
    Csource * (osc + B) = Csource * osc + Csource * B := by ring
    _ ≤ Csource * (Cosc * A) + Csource * B :=
      add_le_add (mul_le_mul_of_nonneg_left hOsc hCs) le_rfl
    _ = Csource * Cosc * A + Csource * B := by ring
    _ ≤ Csource * (Cosc + 1) * A + Csource * (Cosc + 1) * B :=
      add_le_add hTermA hTermB


private theorem aux_good_cell_trace_assembly_response_factor_nonneg
    {d : ℕ} {r se sf nu f : ℝ}
    (hr : 0 < r) (hse : 0 < se) (hsf : 0 ≤ sf) (hnu : 0 ≤ nu) :
    0 ≤ sf / se ∧ 0 ≤ nu + se⁻¹ * r ^ ((d : ℝ) + 2) * f ^ 2 := by
  have hdiv : 0 ≤ sf / se := div_nonneg hsf (le_of_lt hse)
  have hinv : 0 ≤ se⁻¹ := inv_nonneg.mpr (le_of_lt hse)
  have hrpow : 0 ≤ r ^ ((d : ℝ) + 2) := Real.rpow_nonneg (le_of_lt hr) _
  have hfsq : 0 ≤ f ^ 2 := sq_nonneg f
  exact ⟨hdiv, add_nonneg hnu (mul_nonneg (mul_nonneg hinv hrpow) hfsq)⟩

theorem good_cell_trace_response_of_source_bound
    {d : ℕ} {mu : Measure (SpatialCoordinates d)}
    {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm mu} (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (S : Set (SpatialCoordinates d)) (z : SpatialCoordinates d)
    (r alpha beta se sf nu fsup osc Csource Cosc Ce Ctotal : ℝ)
    (hr : 0 < r) (hba : beta ≤ alpha) (hb : 0 < beta)
    (hse : 0 < se) (hsf : 0 ≤ sf) (hnu : 0 ≤ nu) (hf : 0 ≤ fsup)
    (hCs : 0 ≤ Csource) (hCo : 0 ≤ Cosc) (hCe : 0 ≤ Ce)
    (hLinear : Csource * (Cosc + 1) ≤ Ctotal)
    (hQuadratic : 2 * Ce * ((Real.sqrt d) ^ (alpha - beta) *
      (Csource * (Cosc + 1))) ^ 2 ≤ Ctotal)
    (U : SpatialCoordinates d → ℝ)
    (_hUc : ContinuousOn U (frontier (Metric.ball z (r / 2))))
    (hSource : ∃ cq : ℝ,
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ≤
        Csource * (osc + r ^ (2 : ℝ) * se⁻¹ * fsup))
    (hOsc : osc ≤ Cosc * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu)
    (hExtension : IsHolderOn beta (frontier (Metric.ball z (r / 2))) U →
      ∃ (v : MeasureTheory.Lp ℝ 2 mu) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧ ContinuousOn V S ∧ (v : SpatialCoordinates d → ℝ) =ᵐ[mu] V ∧
        (∀ x ∈ frontier (Metric.ball z (r / 2)), V x = U x) ∧
        (Gamma.measure v (Metric.ball z (r / 2))).toReal ≤
          Ce * sf * r ^ ((d : ℝ) - 2) *
            (r ^ beta * holderSeminorm beta (frontier (Metric.ball z (r / 2))) U) ^ 2) :
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
        Ctotal * (sf / se) * (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2) := by
  let A : ℝ :=
    r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu
  let B : ℝ := r ^ (2 : ℝ) * se⁻¹ * fsup
  let K : ℝ := Csource * (Cosc + 1)
  let D : ℝ := (Real.sqrt d) ^ (alpha - beta)
  let C : ℝ := D * K
  obtain ⟨hA, hB, hD⟩ :=
    aux_good_cell_trace_assembly_amplitudes_nonneg hr hse hf
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hCs (by linarith only [hCo])
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hD hK
  obtain ⟨cq, hU, hNorm⟩ := hSource
  have hOscA : osc ≤ Cosc * A := by
    calc
      osc ≤ Cosc * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu := hOsc
      _ = Cosc * A := by dsimp [A]; ring
  have hSourceAmplitude : Csource * (osc + B) ≤ K * A + K * B := by
    have hSourceBound := aux_good_cell_trace_assembly_source_bound hA hB hCs hCo hOscA
    simpa only [K] using hSourceBound
  have hNormBound :
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ≤ K * A + K * B := by
    calc
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
          (fun x => U (z + r • x) - cq) ≤ Csource * (osc + B) := by
            simpa only [B] using hNorm
      _ ≤ K * A + K * B := hSourceAmplitude
  have hScaleInput : 0 ≤ K * A + K * B :=
    add_nonneg (mul_nonneg hK hA) (mul_nonneg hK hB)
  obtain ⟨hHolder, hSem⟩ :=
    SubdiffusiveProcess.scaled_boundary_holderSeminorm_le_normalized_norm
      z r hr alpha beta cq (K * A + K * B) hba hb hScaleInput U hU hNormBound
  let trace : ℝ :=
    r ^ beta * holderSeminorm beta (frontier (Metric.ball z (r / 2))) U
  have hTraceNonneg : 0 ≤ trace := by
    dsimp [trace]
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hr beta))
      (SubdiffusiveProcess.holderSeminorm_nonneg beta
        (frontier (Metric.ball z (r / 2))) U)
  have hTraceBound : trace ≤ C * A + C * B := by
    dsimp [trace]
    calc
      r ^ beta * holderSeminorm beta (frontier (Metric.ball z (r / 2))) U ≤
          D * (K * A + K * B) := by simpa only [D] using hSem
      _ = C * A + C * B := by dsimp [C]; ring
  have hTraceInput :
      trace ≤ C * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu +
        C * r ^ (2 : ℝ) * se⁻¹ * fsup := by
    calc
      trace ≤ C * A + C * B := hTraceBound
      _ = C * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu +
          C * r ^ (2 : ℝ) * se⁻¹ * fsup := by dsimp [A, B]; ring
  have hCoeff : 2 * Ce * C ^ 2 ≤ Ctotal := by
    simpa only [C, D, K] using hQuadratic
  obtain ⟨hDiv, hFactor⟩ :=
    aux_good_cell_trace_assembly_response_factor_nonneg
      (d := d) (r := r) (se := se) (sf := sf) (nu := nu) (f := fsup)
      hr hse hsf hnu
  have hResponse :=
    _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure.continuousTraceValues_le_reference_ratio
      Gamma S (Metric.ball z (r / 2)) U d trace C Ce r se sf nu fsup
      hTraceNonneg hC hCe hr hse hsf hnu hf hTraceInput
      (by simpa only [trace] using hExtension hHolder)
  rcases hResponse with ⟨hNonempty, hGLB, hUpper⟩
  have hResponseTotal :
      sInf (Gamma.continuousTraceValues S (Metric.ball z (r / 2)) U) ≤
        Ctotal * (sf / se) *
          (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2) := by
    calc
      sInf (Gamma.continuousTraceValues S (Metric.ball z (r / 2)) U) ≤
          (2 * Ce * C ^ 2) * (sf / se) *
            (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2) := hUpper
      _ ≤ Ctotal * (sf / se) *
            (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCoeff hDiv) hFactor
  refine ⟨cq, hU, ?_, hNonempty, hGLB, hResponseTotal⟩
  have hLinearCoeff : K ≤ Ctotal := by simpa only [K] using hLinear
  calc
    cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ≤ Csource * (osc + B) := by
          simpa only [B] using hNorm
    _ ≤ K * A + K * B := hSourceAmplitude
    _ ≤ Ctotal * A + Ctotal * B :=
      add_le_add
        (mul_le_mul_of_nonneg_right hLinearCoeff hA)
        (mul_le_mul_of_nonneg_right hLinearCoeff hB)
    _ = Ctotal * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu +
        Ctotal * r ^ (2 : ℝ) * se⁻¹ * fsup := by dsimp [A, B]; ring

end SubdiffusiveProcess
