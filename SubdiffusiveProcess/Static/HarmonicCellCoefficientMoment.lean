module

public import SubdiffusiveProcess.Static.HarmonicCellMomentArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

@[expose] public section

/-! # Arbitrarily small geometric moment cost of the microscopic coefficient envelope -/

open MeasureTheory Homogenization Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- A two-sided absolute-cutoff coefficient envelope on one physical unit cell. -/
def harmonicMicroscopicCellEnvelope {d : ℕ} (M : GMCModel d) (j : ℕ)
    (p : Fin d → ℤ) (omega : PotentialSample d) : ℝ :=
  Real.exp (subunitCellEnvelope j p omega +
    suffixSensitivityRealRepresentative j (j : ℤ) omega + subunitDrift M j)

theorem one_le_harmonicMicroscopicCellEnvelope {d : ℕ} (M : GMCModel d) (j : ℕ)
    (p : Fin d → ℤ) (omega : PotentialSample d) :
    1 ≤ harmonicMicroscopicCellEnvelope M j p omega := by
  apply Real.one_le_exp
  exact add_nonneg (add_nonneg (subunitCellEnvelope_nonneg j p omega)
    ENNReal.toReal_nonneg) (subunitDrift_nonneg M j)

theorem measurable_harmonicMicroscopicCellEnvelope {d : ℕ}
    (M : GMCModel d) (j : ℕ) (p : Fin d → ℤ) :
    Measurable (harmonicMicroscopicCellEnvelope M j p) := by
  exact (((measurable_subunitCellEnvelope j p).add
    ((measurable_suffixSensitivityRealRepresentative j (j : ℤ)).mono
      (potentialShellIndexSigma_le_borel _) le_rfl)).add_const _).exp

/-- The per-cell lognormal price has any prescribed positive geometric
exponent after choosing the disorder threshold for the requested moment. -/
theorem exists_harmonicMicroscopicCellEnvelope_moment_bound (d : ℕ) (q eta : ℝ)
    (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 → ∀ j : ℕ, ∀ p : Fin d → ℤ,
        eLpNorm (harmonicMicroscopicCellEnvelope M j p) (ENNReal.ofReal q) M.P.toMeasure ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (eta * (j : ℝ))) := by
  let S := subunitScaleConst d
  let c := eta * Real.log 3 / 2
  let A := 2 * gammaMomentConst 2 * Real.sqrt (2 * q)
  let C := (1 + A * (S + 1) * c⁻¹) * (3 : ℝ) ^ eta
  let delta0 := min 1 (Real.sqrt (c / (q * S ^ 2 + 1)))
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hS : 0 < S := subunitScaleConst_pos d
  have hgamma : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hc : 0 < c := by dsimp only [c]; exact div_pos (mul_pos heta (Real.log_pos (by norm_num))) (by norm_num)
  have hA : 0 < A := by dsimp only [A]; exact mul_pos (mul_pos (by norm_num)
    (gammaMomentConst_pos (by norm_num))) (Real.sqrt_pos.mpr (by positivity))
  have hden : 0 < q * S ^ 2 + 1 := by positivity
  have hdelta : 0 < delta0 := lt_min (by norm_num) (Real.sqrt_pos.mpr (div_pos hc hden))
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨delta0, C, hdelta, hC, ?_⟩
  intro M hM j p
  have hd1 : M.delta ≤ 1 := hM.trans (min_le_left _ _)
  have hdpos := M.shellPrefix.delta_pos
  have hd2 : M.delta ^ 2 ≤ c / (q * S ^ 2 + 1) := by
    have h := pow_le_pow_left₀ hdpos.le (hM.trans (min_le_right _ _)) 2
    rwa [Real.sq_sqrt (div_pos hc hden).le] at h
  have hsmall : (q * S ^ 2 + 1) * M.delta ^ 2 ≤ c := by
    simpa only [mul_comm] using (le_div_iff₀ hden).mp hd2
  let t := (j : ℝ) + 1
  have ht1 : 1 ≤ t := by dsimp only [t]; linarith [Nat.cast_nonneg (α := ℝ) j]
  have ht : 0 ≤ t := zero_le_one.trans ht1
  have hsqrt : Real.sqrt t ≤ t := by
    nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]
  have hdrift : subunitDrift M j ≤ t * M.delta ^ 2 := by
    have htau := tauSq_le_delta_sq M
    have hlog2 : Real.log 2 / 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    unfold subunitDrift
    have hbound : Real.log 2 / 2 * M.delta ^ 2 ≤ M.delta ^ 2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hlog2 (sq_nonneg M.delta)
    exact mul_le_mul_of_nonneg_left (htau.trans hbound) ht
  have hscale : subunitScale M j ≤ S * t := by
    unfold subunitScale
    calc
      _ ≤ S * 1 * Real.sqrt t := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd1 hS.le) (Real.sqrt_nonneg t)
      _ ≤ S * t := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt hS.le
  have hsum : subunitScale M j + subunitDrift M j ≤ (S + 1) * t := by
    have hd2one : M.delta ^ 2 ≤ 1 := by nlinarith
    have hb := hdrift.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hd2one ht)
    nlinarith only [hscale, hb]
  have hscaleSq : subunitScale M j ^ 2 = S ^ 2 * M.delta ^ 2 * t := by
    unfold subunitScale
    rw [mul_pow, mul_pow, Real.sq_sqrt ht]
  have hexponent : q * subunitScale M j ^ 2 + subunitDrift M j ≤ c * t := by
    rw [hscaleSq]
    have hp := mul_le_mul_of_nonneg_right hsmall ht
    nlinarith only [hdrift, hp]
  have hmajorant0 : ∀ omega : PotentialSample d, 0 ≤ subunitCellMajorant M j p omega := by
    intro omega
    change 0 ≤ harmonicMicroscopicCellEnvelope M j p omega - 1
    exact sub_nonneg.mpr (one_le_harmonicMicroscopicCellEnvelope M j p omega)
  have hmajorantmeas : Measurable (subunitCellMajorant M j p) :=
    (measurable_harmonicMicroscopicCellEnvelope M j p).sub_const 1
  obtain ⟨hmi, hmr⟩ := subunitCellMajorant_moment M j p hq
  have hscale0 := (subunitScale_pos M j).le
  have hdrift0 := subunitDrift_nonneg M j
  have hn := ENNReal.ofReal_le_ofReal hmr
  rw [← eLpNorm_nonneg_eq_ofReal_integral_root M.P.toMeasure _ hmajorant0 hq0 hmi] at hn
  have hconst : eLpNorm (fun _ : PotentialSample d => (1 : ℝ)) (ENNReal.ofReal q)
      M.P.toMeasure = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hq0).ne' (NeZero.ne M.P.toMeasure)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
  have hfeq : harmonicMicroscopicCellEnvelope M j p =
      fun omega => 1 + subunitCellMajorant M j p omega := by
    funext omega
    dsimp only [harmonicMicroscopicCellEnvelope, subunitCellMajorant]
    ring
  rw [hfeq]
  refine (eLpNorm_add_le (f := fun _ => (1 : ℝ)) (g := subunitCellMajorant M j p)
    (ENNReal.one_le_ofReal.mpr hq)).trans ?_
  rw [hconst]
  refine (add_le_add le_rfl hn).trans ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ 1 + (A * (S + 1)) * t * Real.exp (c * t) := by
      dsimp only [A]
      have hb := mul_le_mul hsum (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le
        (by positivity : 0 ≤ (S + 1) * t)
      have hp := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * gammaMomentConst 2 * Real.sqrt (2 * q))
      nlinarith only [hp]
    _ ≤ (1 + (A * (S + 1)) * c⁻¹) * Real.exp (2 * c * t) :=
      linear_mul_exp_le_geometric (by positivity) hc ht
    _ = C * (3 : ℝ) ^ (eta * (j : ℝ)) := by
      have he : Real.exp (2 * c * t) = (3 : ℝ) ^ eta * (3 : ℝ) ^ (eta * (j : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
          Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
        congr 1
        dsimp only [c, t]
        ring
      rw [he]
      dsimp only [C]
      ring

end SubdiffusiveProcess.Static
