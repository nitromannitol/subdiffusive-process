module

public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue
public import Homogenization.Besov.Duality.GlobalComparison
public import Homogenization.Sobolev.Foundations.CubeBesovPoincare

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov

open MeasureTheory
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The dimensional constant -/

/-- The scale-free dimensional constant of the function-level multiscale
Poincare estimate: the cube full-dual vector Poincare constant times the
upstream full-dual-to-circ comparison constant at `s = 1`. -/
noncomputable def oscillationMultiscalePoincareConstant (d : ℕ) [NeZero d] : ℝ :=
  (d : ℝ) * Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d *
    (3 : ℝ) ^ ((d : ℝ) + 1)

theorem oscillationMultiscalePoincareConstant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ oscillationMultiscalePoincareConstant d := by
  unfold oscillationMultiscalePoincareConstant
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg d)
      (Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d))
    (Real.rpow_nonneg (by norm_num) _)

variable [NeZero d]

/-! ## The oscillation bound -/

private theorem conjExponent_two_eq : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

/-- **The function-level multiscale Poincare estimate.**  The normalized `L²`
oscillation of a `W^{1,2}` function on a triadic cube is bounded by a scale-free
dimensional constant times the sum over coordinates of the negative circ Besov
norm at `(s,p,q) = (1,2,1)` of the corresponding partial derivative, which is
the manuscript's multiscale sum of gradient cube averages for that coordinate,
weighted by `3^{Q.scale}`. -/
theorem cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x) ≤
      oscillationMultiscalePoincareConstant d *
        ∑ i : Fin d, cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) := by
  have hC0 : 0 ≤ fullVectorPoincareCubeConstant Q := fullVectorPoincareCubeConstant_nonneg Q
  have hcoord : ∀ i : Fin d,
      cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) ≤
        (3 : ℝ) ^ ((d : ℝ) + 1) *
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) := by
    intro i
    exact cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm
      Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) (by norm_num)
      (u.grad_memL2_normalizedCubeMeasure i) (by norm_num) (by norm_num)
      (by rw [conjExponent_two_eq]; norm_num) (by norm_num)
  calc
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x)
        ≤ fullVectorPoincareCubeConstant Q *
            ∑ i : Fin d,
              cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) :=
          CubeDualFullVectorPoincareEstimate.of_h1Function Q u
    _ ≤ fullVectorPoincareCubeConstant Q *
            ∑ i : Fin d,
              (3 : ℝ) ^ ((d : ℝ) + 1) *
                cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcoord i) hC0
    _ = oscillationMultiscalePoincareConstant d *
            ∑ i : Fin d, cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) := by
          rw [← Finset.mul_sum, oscillationMultiscalePoincareConstant,
            fullVectorPoincareCubeConstant_eq_dimensionConstant Q]
          ring

/-! ## The Caccioppoli right-hand side -/

omit [NeZero d] in
/-- The normalized `L²` square of the centred function on the open cube, which
is the carrier of the Caccioppoli right-hand side, is the square of the cube
oscillation. -/
theorem normalizedL2SqOnSet_openCubeSet_centred_eq_cubeBesovOscillation_sq
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    normalizedL2SqOnSet (openCubeSet Q)
        (fun x => u.toFun x - cubeAverage Q (fun x => u.toFun x)) =
      cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x) ^ 2 := by
  let : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hmem := u.memL2_normalizedCubeMeasure
  have hfluc :
      MemLp (fun x => u.toFun x - cubeAverage Q (fun x => u.toFun x)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    hmem.sub (memLp_const _)
  simpa [cubeBesovOscillation, cubeFluctuation] using!
    normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q _ hfluc

/-- **The Caccioppoli right-hand side in multiscale form.**  The parent-cube
oscillation `L²` square that the coarse-grained Caccioppoli estimate leaves on
the right is bounded by the square of the coordinate-summed multiscale average
sum of the solution gradient. -/
theorem interiorCaccioppoliParentOscillationL2Sq_le_sq_sum_cubeBesovCircNorm
    (Q : TriadicCube d) (a : CoeffFamily d) (v : CubeSolution Q a) :
    interiorCaccioppoliParentOscillationL2Sq Q a v ≤
      (oscillationMultiscalePoincareConstant d *
          ∑ i : Fin d,
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => v.toH1.grad x i)) ^ 2 := by
  have heq :
      interiorCaccioppoliParentOscillationL2Sq Q a v =
        cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => v.toH1.toFun x) ^ 2 :=
    normalizedL2SqOnSet_openCubeSet_centred_eq_cubeBesovOscillation_sq Q v.toH1
  rw [heq]
  exact pow_le_pow_left₀ (cubeBesovOscillation_nonneg Q (2 : ℝ≥0∞) _)
    (cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm
      Q v.toH1) 2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
