module

public import SubdiffusiveProcess.Besov.CenteredTruncation

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- The centering correction is bounded by the original root L1 fluctuation. -/
theorem clippedPart_mean_abs_le {d : ℕ} (Q : TriadicCube d) (n : ℕ)
    (g : Vec d → ℝ) (hg : IntegrableOn g (cubeSet Q)) :
    |cubeAverage Q (clippedPart Q n g)| ≤
      cubeAverage Q (fun x => |g x - cubeAverage Q g|) := by
  have hshift := (integrable_normalizedCubeMeasure Q hg).sub (integrable_const (cubeAverage Q g))
  have hc := integrable_clip (normalizedCubeMeasure Q) hshift (by positivity : 0 ≤ (n : ℝ) + 1)
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  calc
    _ ≤ ∫ x, ‖clippedPart Q n g x‖ ∂normalizedCubeMeasure Q := norm_integral_le_integral_norm _
    _ ≤ _ := integral_mono hc.norm hshift.norm (fun x => by
      simp only [Real.norm_eq_abs]
      exact clip_abs_le (by positivity : 0 ≤ (n : ℝ) + 1)
        (g x - cubeAverage Q g))

/-- A bound independent of the truncation depth. -/
theorem centeredTruncation_abs_le {d : ℕ} (Q : TriadicCube d) (n : ℕ)
    (g : Vec d → ℝ) (hg : IntegrableOn g (cubeSet Q)) (x : Vec d) :
    |centeredTruncation Q n g x| ≤ |g x| +
      (2 * |cubeAverage Q g| + cubeAverage Q (fun y => |g y - cubeAverage Q g|)) := by
  have hc := clip_abs_le (by positivity : 0 ≤ (n : ℝ) + 1) (g x - cubeAverage Q g)
  have hm := clippedPart_mean_abs_le Q n g hg
  have hs : |g x - cubeAverage Q g| ≤ |g x| + |cubeAverage Q g| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (g x) 0 (cubeAverage Q g)
  have ht : |cubeAverage Q g - cubeAverage Q (clippedPart Q n g)| ≤
      |cubeAverage Q g| + |cubeAverage Q (clippedPart Q n g)| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (cubeAverage Q g) 0
      (cubeAverage Q (clippedPart Q n g))
  have ha := abs_add_le (clippedPart Q n g x)
    (cubeAverage Q g - cubeAverage Q (clippedPart Q n g))
  change |clippedPart Q n g x + _| ≤ _
  change |clippedPart Q n g x| ≤ _ at hc
  linarith

/-- The clipped root means converge to zero. -/
theorem tendsto_clippedPart_mean {d : ℕ} (Q : TriadicCube d) (g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet Q)) :
    Filter.Tendsto (fun n => cubeAverage Q (clippedPart Q n g)) Filter.atTop (𝓝 0) := by
  let μ := normalizedCubeMeasure Q
  let h : Vec d → ℝ := fun x => g x - cubeAverage Q g
  have hh : Integrable h μ := (integrable_normalizedCubeMeasure Q hg).sub (integrable_const _)
  have hmean : (∫ x, h x ∂μ) = 0 := by
    rw [integral_sub (integrable_normalizedCubeMeasure Q hg) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul,
      ← cubeAverage_eq_integral_normalizedCubeMeasure]
    exact sub_self _
  have hlim := tendsto_integral_of_dominated_convergence (fun x => |h x|)
    (fun n => (clip_lipschitz (n + 1)).continuous.comp_aestronglyMeasurable hh.aestronglyMeasurable)
    hh.norm
    (fun n => Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using clip_abs_le (by positivity : 0 ≤ (n : ℝ) + 1) (h x))
    (Filter.Eventually.of_forall fun x => tendsto_clip (h x))
  rw [hmean] at hlim
  simpa only [cubeAverage_eq_integral_normalizedCubeMeasure, clippedPart, μ, h] using hlim

/-- The centered truncations converge pointwise to the original function. -/
theorem tendsto_centeredTruncation {d : ℕ} (Q : TriadicCube d) (g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet Q)) (x : Vec d) :
    Filter.Tendsto (fun n => centeredTruncation Q n g x) Filter.atTop (𝓝 (g x)) := by
  have h := (tendsto_clip (g x - cubeAverage Q g)).add
    ((tendsto_const_nhds (x := cubeAverage Q g)).sub (tendsto_clippedPart_mean Q g hg))
  simpa only [centeredTruncation, clippedPart, sub_zero, sub_add_cancel] using h

/-- Dominated convergence for the pairing with centered truncations. -/
theorem tendsto_pairing_centeredTruncation {d : ℕ} (Q : TriadicCube d) (f g : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet Q)) (hg : IntegrableOn g (cubeSet Q))
    (hfg : IntegrableOn (fun x => f x * g x) (cubeSet Q)) :
    Filter.Tendsto (fun n => cubeBesovPairing Q f (centeredTruncation Q n g))
      Filter.atTop (𝓝 (cubeBesovPairing Q f g)) := by
  let μ := normalizedCubeMeasure Q
  let K := 2 * |cubeAverage Q g| + cubeAverage Q (fun x => |g x - cubeAverage Q g|)
  let F : ℕ → Vec d → ℝ := fun n x => f x * centeredTruncation Q n g x
  let bound : Vec d → ℝ := fun x => |f x * g x| + K * |f x|
  have hfμ := integrable_normalizedCubeMeasure Q hf
  have hfgμ := integrable_normalizedCubeMeasure Q hfg
  have hb : Integrable bound μ := hfgμ.norm.add (hfμ.norm.const_mul K)
  have hm : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    exact hfμ.aestronglyMeasurable.mul
      (integrable_normalizedCubeMeasure Q (centeredTruncation_integrable Q n g hg)).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x := by
    intro n
    apply Filter.Eventually.of_forall
    intro x
    have h := mul_le_mul_of_nonneg_left (centeredTruncation_abs_le Q n g hg x) (abs_nonneg (f x))
    simpa only [F, bound, K, Real.norm_eq_abs, abs_mul, mul_add, mul_comm] using h
  have hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (f x * g x)) :=
    Filter.Eventually.of_forall fun x => tendsto_const_nhds.mul (tendsto_centeredTruncation Q g hg x)
  have h := tendsto_integral_of_dominated_convergence bound hm hb hbound hlim
  simpa only [cubeBesovPairing, cubeAverage_eq_integral_normalizedCubeMeasure, μ, F] using h

end SubdiffusiveProcess.Besov
