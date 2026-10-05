module

public import SubdiffusiveProcess.Static.CutoffUnitCoercivity
public import SubdiffusiveProcess.Static.DyadicCoercivityAssembly
public import SubdiffusiveProcess.Static.AffineCoercivity
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4Envelope

@[expose] public section

/-! # Native unweighted cube coercivity -/

open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- A deterministic Sobolev constant extracted from the native unit readout.
Its dependence on the fixed model is harmless in the bounded microscopic
scale branch, where the static principal permits its moment bound after M. -/
theorem exists_unit_unweighted_coercivity {d : ℕ} [NeZero d] (M : GMCModel d) :
    ∃ D : ℝ, 0 < D ∧ cubeCoercivityEstimates (fun _ : Vec d => 1) 0 1 D := by
  obtain ⟨D0, hD0, hunit⟩ := exists_cutoff_unit_coercivity_constant d
  obtain ⟨ω, hω⟩ := (hunit M 0 0 0).exists
  let K := 1 + D0 * cutoffLowerInv M 0 0 0 ω
  have hK : 1 ≤ K := le_add_of_nonneg_right
    (mul_nonneg hD0.le (cutoffLowerInv_nonneg M 0 0 0 ω))
  let E := aCutoffCubeLogEnvelope M 0 0 ω
  let F := 1 + (ahom M 0)⁻¹ * Real.exp E
  have hF : 1 ≤ F := le_add_of_nonneg_right (by
    have := ahom_pos M 0
    positivity)
  have hA : ∀ x ∈ openCubeSet (originCube d 0),
      (ahom M 0)⁻¹ * aCutoff M 0 (translatePotentialSample 0 ω) ((3 : ℝ) ^ 0 • x) ≤
        F * (1 : ℝ) := by
    intro x hx
    simp only [pow_zero, one_smul, SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.aCutoff_translatePotentialSample,
      add_zero, mul_one]
    have ha := aCutoff_le_exp_aCutoffCubeLogEnvelope M 0 0 ω hx
    exact (mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr (ahom_pos M 0).le)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨K * F, mul_pos (zero_lt_one.trans_le hK) (zero_lt_one.trans_le hF), ?_⟩
  unfold cubeCoercivityEstimates
  rw [← unitCube_eq_ball]
  constructor
  · intro H
    have hE := energy_le_mul (isOpen_openCubeSet _).measurableSet (zero_le_one.trans hF) hA H.grad
    have hL : (∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (H.toFun x ^ 2)) ≤
        ENNReal.ofReal F * ∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (H.toFun x ^ 2) := by
      simpa only [one_mul] using mul_le_mul_left (ENNReal.one_le_ofReal.mpr hF)
        (∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (H.toFun x ^ 2))
    refine ((hω.1 H).trans (mul_le_mul_right (add_le_add hE hL) _)).trans_eq ?_
    rw [← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul (zero_le_one.trans hK)]
  · intro H
    have hE := energy_le_mul (isOpen_openCubeSet _).measurableSet (zero_le_one.trans hF) hA H.grad
    refine ((hω.2 H).trans (mul_le_mul_right hE _)).trans_eq ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (zero_le_one.trans hK)]

end SubdiffusiveProcess.Static
