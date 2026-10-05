module

public import SubdiffusiveProcess.Section10.EndpointPathsConsumer
public import SubdiffusiveProcess.Section10.ExitMomentPassage
public import Mathlib.Analysis.PSeries

@[expose] public section

open Filter MeasureTheory Topology Set SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.EndpointPaths

/-- The mean decay supplies the summability input of the existing Markov/BC
theorem. The positive shift excludes the literal zero threshold at k = 0. -/
theorem summable_exit_ratios_of_mean_decay {d : ℕ}
    (P : Measure (DiffusionPath d)) (C eta epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hmean : ∀ k : ℕ, (∫⁻ w, smallExit k w ∂P) ≤
      ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    (∑' n : ℕ, (∫⁻ w, smallExit (n+1) w ∂P) /
      ENNReal.ofReal (endpoint eta epsilon (n+1))) ≠ ⊤ := by
  have hs : Summable (fun n : ℕ => C / ((n+1 : ℕ) : ℝ)^(1+epsilon)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (1+epsilon)).mpr (by linarith)
    have hn : ∀ n : ℕ, 0 ≤ (n : ℝ)+1 := fun _ => by positivity
    simpa only [Nat.cast_add, Nat.cast_one, abs_of_nonneg (hn _), mul_one_div]
      using h.mul_left C
  apply ne_top_of_le_ne_top hs.tsum_ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro n
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hg : 0 < (3 : ℝ)^(-((2+eta)*((n+1 : ℕ) : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc
    _ ≤ ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*((n+1 : ℕ) : ℝ)))) /
        ENNReal.ofReal (endpoint eta epsilon (n+1)) :=
      ENNReal.div_le_div_right (hmean (n+1)) _
    _ = ENNReal.ofReal (C / ((n+1 : ℕ) : ℝ)^(1+epsilon)) := by
      rw [← ENNReal.ofReal_div_of_pos (endpoint_pos eta epsilon (by omega))]
      congr 1
      dsimp only [endpoint]
      field_simp [(Real.rpow_pos_of_pos hn (1+epsilon)).ne', hg.ne']

/-- Complete generic application with precisely the same eta and epsilon.
No new Borel--Cantelli theorem is introduced. -/
theorem ae_endpoint_consequences_of_mean_decay {d : ℕ}
    (P : Measure (DiffusionPath d)) (C eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hmean : ∀ k : ℕ, (∫⁻ w, smallExit k w ∂P) ≤
      ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    ∀ᵐ w ∂P,
      (∀ᶠ t : ℝ≥0 in 𝓝[>] 0,
        oscillationConstant eta epsilon *
          ((t : ℝ) / Real.log (1 / (t : ℝ))^(1+epsilon))^(1/(2+eta)) ≤ maximum t w) ∧
      Tendsto (fun t : ℝ≥0 => maximum t w / Real.sqrt t) (𝓝[>] 0) atTop ∧
      (∀ gamma : ℝ, 0 ≤ gamma →
        (fun t : ℝ≥0 => Homogenization.euclideanNorm (w t - w 0))
          =O[𝓝[>] 0] (fun t : ℝ≥0 => (t : ℝ)^gamma) → gamma ≤ 1/(2+eta)) ∧
      (∀ᶠ k : ℕ in atTop, smallExit k w ≤ ENNReal.ofReal (endpoint eta epsilon k)) := by
  exact ae_endpoint_consequences P eta epsilon heta hepsilon
    (fun n => by simpa only [ENNReal.rpow_one] using
      (ExitMomentPassage.smallExit_rpow_lsc (n+1) 1 (by norm_num)).measurable)
    (summable_exit_ratios_of_mean_decay P C eta epsilon hepsilon hmean)

end SubdiffusiveProcess.Section10.EndpointPaths
