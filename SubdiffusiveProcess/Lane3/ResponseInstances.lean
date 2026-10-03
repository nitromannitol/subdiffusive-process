module

public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Lane3.LocalEnergyAux
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import Mathlib.Tactic

@[expose] public section

/-!
# The two concrete responses of the paper are `Lane3.Response`s

`mfd:sec-resampling`: a response is
either a Dirichlet response `Λ_{N,Q}(g)` or a killed inverse response
`⟨f, G_N^Q f⟩`.  Here both are packaged as `Lane3.Response`, with energy
measure the local gradient energy of the corresponding minimizer.  Every field
is discharged from the already proved
`boundary_responses_potential_stability`, `source_responses_potential_stability`
(`eq:mfd-14`) and `dirichletResponse_potential_comparison`,
`inverseResponse_potential_comparison` (`eq:mfd-mult`).
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess
namespace Lane3

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- `δ² / c² = S² e^{4S}` for `δ = S e^{S}`, `c = e^{-S}`. -/
theorem delta_sq_div_c_sq (Sn : ℝ) :
    (Sn * Real.exp Sn) ^ 2 / Real.exp (-Sn) ^ 2 = Sn ^ 2 * Real.exp (4 * Sn) := by
  have e1 : Real.exp Sn ^ 2 = Real.exp (2 * Sn) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (-Sn) ^ 2 = Real.exp (-(2 * Sn)) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have e3 : (2 : ℝ) * Sn + 2 * Sn = 4 * Sn := by ring
  rw [mul_pow, e1, e2, Real.exp_neg, div_inv_eq_mul, mul_assoc, ← Real.exp_add, e3]

/-- `δ + δ² / c = S e^{S} + S² e^{3S}` for `δ = S e^{S}`, `c = e^{-S}`. -/
theorem delta_add_sq_div_c (Sn : ℝ) :
    Sn * Real.exp Sn + (Sn * Real.exp Sn) ^ 2 / Real.exp (-Sn) =
      Sn * Real.exp Sn + Sn ^ 2 * Real.exp (3 * Sn) := by
  have e1 : Real.exp Sn ^ 2 = Real.exp (2 * Sn) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have e3 : (2 : ℝ) * Sn + Sn = 3 * Sn := by ring
  rw [mul_pow, e1, Real.exp_neg, div_inv_eq_mul, mul_assoc, ← Real.exp_add, e3]

/-- `S e^{S} + S² e^{3S} ≤ 2 S e^{4S}`: the paper's constant `2 S e^{4S}` of
`eq:mfd-14`, paper line 1305, dominates the constant the Lean carrier proves. -/
theorem response_constant_le {Sn : ℝ} (hS : 0 ≤ Sn) :
    Sn * Real.exp Sn + Sn ^ 2 * Real.exp (3 * Sn) ≤ 2 * Sn * Real.exp (4 * Sn) := by
  have hexp : Sn ≤ Real.exp Sn := by
    have := Real.add_one_le_exp Sn
    linarith
  have h1 : Real.exp Sn ≤ Real.exp (4 * Sn) := Real.exp_le_exp.mpr (by linarith)
  have h34 : Real.exp Sn * Real.exp (3 * Sn) = Real.exp (4 * Sn) := by
    rw [← Real.exp_add]; ring_nf
  have hA : Sn * Real.exp Sn ≤ Sn * Real.exp (4 * Sn) :=
    mul_le_mul_of_nonneg_left h1 hS
  have hB : Sn ^ 2 * Real.exp (3 * Sn) ≤ Sn * Real.exp (4 * Sn) := by
    have hpos : (0 : ℝ) < Real.exp (3 * Sn) := Real.exp_pos _
    calc Sn ^ 2 * Real.exp (3 * Sn) = Sn * (Sn * Real.exp (3 * Sn)) := by ring
      _ ≤ Sn * (Real.exp Sn * Real.exp (3 * Sn)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hpos.le) hS
      _ = Sn * Real.exp (4 * Sn) := by rw [h34]
  linarith

/-- The Dirichlet response of the paper, packaged as a `Lane3.Response`. -/
def dirichletResponseData (S : ResponseSpace Ω) (b : weakSobolevGraph Ω) :
    Response Ω where
  eval g := dirichletResponse S (expPotentialCoefficient g) b
  mass g s := if hs : MeasurableSet s then
      localGradientEnergy (expPotentialCoefficient g) hs
        (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient g) b).val)
    else 0
  eval_nonneg g := dirichletResponse_nonneg S _ b
  mass_nonneg g s := by
    by_cases hs : MeasurableSet s
    · rw [dif_pos hs]; exact localGradientEnergy_nonneg _ hs _
    · rw [dif_neg hs]
  mass_mono g s t hs ht hst := by
    rw [dif_pos hs, dif_pos ht]
    exact localGradientEnergy_mono _ hs ht hst _
  mass_univ g := by
    rw [dif_pos MeasurableSet.univ, localGradientEnergy_univ]
    rfl
  exp_comparison g h := by
    have hc := (dirichletResponse_potential_comparison S b h g).2
    rwa [norm_sub_rev h g] at hc
  response_perturbation h g s hs hsupp := by
    have hst := (boundary_responses_potential_stability S h g hs hsupp b).2.2
    rw [dif_pos hs]
    refine hst.trans (mul_le_mul_of_nonneg_right ?_ (localGradientEnergy_nonneg _ hs _))
    rw [delta_add_sq_div_c]
    exact response_constant_le (norm_nonneg g)
  mass_perturbation h g s hs hsupp := by
    have hst := (boundary_responses_potential_stability S h g hs hsupp b).2.1
    rw [dif_pos hs, dif_pos hs]
    rwa [delta_sq_div_c_sq] at hst

/-- The killed inverse response of the paper, packaged as a `Lane3.Response`. -/
def inverseResponseData (S : ResponseSpace Ω) (L : S.space →L[ℝ] ℝ) :
    Response Ω where
  eval g := inverseResponse S (expPotentialCoefficient g) L
  mass g s := if hs : MeasurableSet s then
      localGradientEnergy (expPotentialCoefficient g) hs
        (subspaceGradient S.space (responseSolution S (expPotentialCoefficient g) L))
    else 0
  eval_nonneg g := inverseResponse_nonneg S _ L
  mass_nonneg g s := by
    by_cases hs : MeasurableSet s
    · rw [dif_pos hs]; exact localGradientEnergy_nonneg _ hs _
    · rw [dif_neg hs]
  mass_mono g s t hs ht hst := by
    rw [dif_pos hs, dif_pos ht]
    exact localGradientEnergy_mono _ hs ht hst _
  mass_univ g := by
    rw [dif_pos MeasurableSet.univ, localGradientEnergy_univ]
    rfl
  exp_comparison g h := by
    have hc := (inverseResponse_potential_comparison S L h g).2
    rwa [norm_sub_rev h g] at hc
  response_perturbation h g s hs hsupp := by
    have hst := (source_responses_potential_stability S h g hs hsupp L).2.2
    rw [dif_pos hs]
    refine hst.trans (mul_le_mul_of_nonneg_right ?_ (localGradientEnergy_nonneg _ hs _))
    rw [delta_add_sq_div_c]
    exact response_constant_le (norm_nonneg g)
  mass_perturbation h g s hs hsupp := by
    have hst := (source_responses_potential_stability S h g hs hsupp L).2.1
    rw [dif_pos hs, dif_pos hs]
    rwa [delta_sq_div_c_sq] at hst

end Lane3
end SubdiffusiveProcess
