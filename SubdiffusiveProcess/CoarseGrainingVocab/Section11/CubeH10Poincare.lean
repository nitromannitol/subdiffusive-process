module

public import Homogenization.Sobolev.MatchedPair.ScaledPoincare
public import Homogenization.Sobolev.Foundations.DifferenceQuotient
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

/-!
# Scale-explicit zero-trace Poincaré on cubes

The unit-cube Dirichlet constant is transported by the existing translation
and dilation theorem. Squaring and finite-dimensional Cauchy–Schwarz put its
coordinate-gradient norm in the integral-energy vocabulary of Section 11.
-/

open Homogenization MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11

open Section9SupportInput

variable {d : ℕ} {U : Set (Vec d)}

/-- The unweighted energy is the sum of the squared coordinate `L²` norms. -/
theorem energy_one_eq_sum_coordNorm_sq (f : H1Function U) :
    energy (fun _ => 1) U f =
      ∑ i : Fin d, (eLpNorm (fun x => f.grad x i) 2 (volumeMeasureOn U)).toReal ^ 2 := by
  simp only [energy, one_mul, vecDot, ← sq]
  rw [integral_finset_sum _ (fun i _ => (f.gradMemL2 i).integrable_sq)]
  exact Finset.sum_congr rfl fun i _ =>
    (toReal_eLpNorm_two_sq_eq_integral_sq (f.gradMemL2 i)).symm

/-- Cauchy–Schwarz converts the sum of coordinate norms to the Euclidean energy. -/
theorem sum_coordNorm_sq_le_energy (f : H1Function U) :
    (∑ i : Fin d, (eLpNorm (fun x => f.grad x i) 2 (volumeMeasureOn U)).toReal) ^ 2 ≤
      (d : ℝ) * energy (fun _ => 1) U f := by
  rw [energy_one_eq_sum_coordNorm_sq]
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin d => (1 : ℝ))
    (fun i => (eLpNorm (fun x => f.grad x i) 2 (volumeMeasureOn U)).toReal)

/-- The dimension-only constant obtained from unit-cube Dirichlet Poincaré. -/
def cubeH10PoincareConst (d : ℕ) [NeZero d] : ℝ :=
  unitDirichletPoincareConst d ^ 2 * d

theorem cubeH10PoincareConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ cubeH10PoincareConst d := by
  unfold cubeH10PoincareConst
  positivity

/-- Scale-explicit integral Poincaré for zero-trace `H¹` functions on an axis cube.
The constant depends only on the dimension, and the side contributes exactly `L²`. -/
theorem h10_poincare_axisCube [NeZero d] (z : Vec d) {L : ℝ} (hL : 0 < L)
    (f : H10Function (axisCube z L)) :
    (∫ x in axisCube z L, f.toH1Function.toFun x ^ 2) ≤
      cubeH10PoincareConst d * L ^ 2 *
        energy (fun _ => 1) (axisCube z L) f.toH1Function := by
  have hn := scaled_dirichlet_poincare z hL f
  have hsq := pow_le_pow_left₀ ENNReal.toReal_nonneg hn 2
  rw [toReal_eLpNorm_two_sq_eq_integral_sq f.toH1Function.memL2,
    mul_pow] at hsq
  have hcs := sum_coordNorm_sq_le_energy f.toH1Function
  calc
    _ ≤ (unitDirichletPoincareConst d * L) ^ 2 *
        (∑ i : Fin d, (eLpNorm (fun x => f.toH1Function.grad x i) 2
          (volumeMeasureOn (axisCube z L))).toReal) ^ 2 := hsq
    _ ≤ (unitDirichletPoincareConst d * L) ^ 2 *
        ((d : ℝ) * energy (fun _ => 1) (axisCube z L) f.toH1Function) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by unfold cubeH10PoincareConst; ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section11
