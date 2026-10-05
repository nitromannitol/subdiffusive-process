module

public import SubdiffusiveProcess.MeyersRegularity.Basic

@[expose] public section

/-! Interior Meyers regularity: Parameters. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

open CubeCalderonZygmund

theorem exists_small_positive_square {A θ : ℝ} (hA : 0 ≤ A) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ A*δ^2 ≤ θ/2 := by
  let δ : ℝ := min (1/2) (θ / (2*(A+1)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hθ (by positivity))
  have hδhalf : δ ≤ 1/2 := min_le_left _ _
  have hδbound : δ*(2*(A+1)) ≤ θ :=
    (le_div_iff₀ (by positivity : 0 < 2*(A+1))).mp (min_le_right _ _)
  refine ⟨δ, hδ, hδhalf, ?_⟩
  have hsq : δ^2 ≤ δ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hA
  nlinarith

theorem exists_absorption_parameters (d : ℕ) (hd : 2 ≤ d) (p θ : ℝ)
    (hp : 2 < p) (hθ : 0 < θ) :
    ∃ q : FiniteLpExponent, ∃ depth : ℕ,
    ∃ G : INTERNAL.HarmonicEuclideanGradientGain d q depth,
    ∃ M eps δ : ℝ, p < q.exponent.toReal ∧ 1 < M ∧ 0 < eps ∧ eps ≤ 1 ∧
      0 < δ ∧ δ ≤ 1/2 ∧
      let κ := oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M/2)^(2-q.exponent.toReal)) + ENNReal.ofReal (eps^2))
      ((2*M)^(p-2) * κ.toReal +
        ((2*M/eps)^(p-2) * eps⁻¹^2) * κ.toReal * (2 : ℝ)^p * δ^2) ≤ θ := by
  let q : FiniteLpExponent := ⟨ENNReal.ofReal (p+1), by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < p+1)]
    linarith, ENNReal.ofReal_lt_top⟩
  have hq : q.exponent.toReal = p+1 := ENNReal.toReal_ofReal (by linarith)
  obtain ⟨⟨depth, G⟩⟩ := INTERNAL.nonempty_harmonicEuclideanGradientGain_finiteTarget_of_two_le d hd q
  let C : ℝ≥0∞ := ENNReal.ofReal (2/θ) * oneStoppingBallCoefficient depth G
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (oneStoppingBallCoefficient_ne_top G)
  obtain ⟨M, eps, hM, heps, heps1, hsmall⟩ :=
    INTERNAL.exists_strict_goodLambda_parameters (r := q.exponent.toReal) hC hp (by rw [hq]; linarith)
  let κ : ℝ≥0∞ := oneStoppingBallCoefficient depth G *
    (ENNReal.ofReal ((M/2)^(2-q.exponent.toReal)) + ENNReal.ofReal (eps^2))
  have hκ : κ ≠ ⊤ := ENNReal.mul_ne_top (oneStoppingBallCoefficient_ne_top G)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  have heq : C * (ENNReal.ofReal ((M/2)^(2-q.exponent.toReal)) + ENNReal.ofReal (eps^2)) *
      ENNReal.ofReal ((2*M)^(p-2)) =
      ENNReal.ofReal (2/θ) * κ * ENNReal.ofReal ((2*M)^(p-2)) := by
    dsimp only [C, κ]
    ac_rfl
  rw [heq] at hsmall
  have hsreal := (ENNReal.toReal_lt_toReal
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hκ) ENNReal.ofReal_ne_top)
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).mpr hsmall
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2/θ),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (by linarith : 0 ≤ 2*M) _), ENNReal.toReal_one] at hsreal
  have hfirst : (2*M)^(p-2) * κ.toReal < θ/2 := by
    have heq' : (2/θ) * κ.toReal * (2*M)^(p-2) =
        (2*((2*M)^(p-2)*κ.toReal))/θ := by ring
    rw [heq', div_lt_iff₀ hθ] at hsreal
    linarith
  let A : ℝ := ((2*M/eps)^(p-2) * eps⁻¹^2) * κ.toReal * (2 : ℝ)^p
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨δ, hδ, hδhalf, hδsmall⟩ := exists_small_positive_square hA hθ
  refine ⟨q, depth, G, M, eps, δ, ?_, hM, heps, heps1, hδ, hδhalf, ?_⟩
  · rw [hq]; linarith
  · change (2*M)^(p-2)*κ.toReal + A*δ^2 ≤ θ
    linarith


end SubdiffusiveProcess.MeyersRegularity
