module

public import SubdiffusiveProcess.Paper.inputs_det_local_error
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRow

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

theorem inputs_det_local_ellipticity (d : ℕ) [NeZero d] (Cerr : ℝ) (hCerr : 0 < Cerr) :
    (∃ E B : ℝ, 0 < E ∧ 0 < B ∧
      ∀ (s : ℝ), 0 < s → s ≤ (1 / 4 : ℝ) →
      ∀ (m n : ℕ) (z x y : Vec d),
        x ∈ truncatedCube d m ((n : ℤ) - 3) z → y ∈ truncatedCube d m n x →
      ∀ (a : Vec d → ℝ) (data : ScalarTriadicCoeffData (fun q => a (q + z)))
        (dataY : ScalarTriadicCoeffData (fun q => a (q + y))) (a0 : ℝ), 0 < a0 →
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
        (s / 8) Ch02.MultiscaleExponent.infinity (.finite 2) data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr →
      let Q := originCube d ((n : ℤ) - 2);
      let A := dataY.toTriadicCoeffFamily;
      Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
            (scalarMatrix (d := d) a0) ≤ E ∧
        a0⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B ∧
        a0 * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B ∧
        Ch02.LambdaS Q (1 / 2) A ≤ B * a0 ∧
        (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * a0⁻¹ ∧
        Ch02.lambdaS Q (s / 3) A ≤ B * a0 ∧
        Ch02.ThetaRatio Q (1 / 2) (s / 3) A ≤ B ^ (2 : ℕ)) := by
  let E : ℝ := Real.sqrt (192 * (d : ℝ)) * (3 * Cerr)
  let B : ℝ := 2 * (d : ℝ) * (E ^ 2 + 1)
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hE : 0 < E := by dsimp [E]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨E, B, hE, hB, ?_⟩
  intro s hs hsle m n z x y hx hy a data dataY a0 ha0 herr
  let err := paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
    (s / 8) Ch02.MultiscaleExponent.infinity (.finite 2) data.toTriadicCoeffFamily a0
  have hfin : err ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top herr
  have hreal : err.toReal ≤ Cerr := ENNReal.toReal_le_of_le_ofReal hCerr.le herr
  have hloc := inputs_det_local_error d s hs hsle m n z x y hx hy a data dataY a0 ha0 hfin
  have hpow : (3 : ℝ) ^ (s / 2) ≤ 3 := by
    calc
      _ ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 3 := by norm_num
  have hcap : Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
      .infinity (.finite 2) dataY.toTriadicCoeffFamily (scalarMatrix (d := d) a0) ≤ E := by
    refine hloc.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans
      (mul_le_mul_of_nonneg_left hreal (by norm_num))
  have hcaps := SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.localBoundaryEllipticityCaps_of_errorCap
    (originCube d ((n : ℤ) - 2)) dataY.toTriadicCoeffFamily hs hsle ha0 hcap
  exact ⟨hcap, hcaps⟩

end SubdiffusiveProcess.Paper

