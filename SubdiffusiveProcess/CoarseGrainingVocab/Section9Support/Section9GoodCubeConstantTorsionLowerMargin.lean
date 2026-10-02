import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2
/-!

Finite L2 carriers and a positive relative inner volume turn a normalized comparison into the strict local norm margin. The scalar budget pays the correction and harmonic oscillation at the same physical scale.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Filter Set SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A positive relative volume yields the strict L2 margin used to find a witness point. -/
theorem goodCube_strict_local_l2_margin
    {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    (hUpos : 0 < (volume U).toReal) (hUfin : volume U ≠ ∞)
    {v0 c0 T : ℝ} (hv0 : 0 < v0) (hc0 : 0 < c0) (hT : 0 < T)
    (hvol : ENNReal.ofReal v0 * volume U ≤ volume V)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hnorm : normalizedL2On U f ≤ (c0 / 8) * Real.sqrt v0 * T) :
    eLpNorm f 2 (volume.restrict U) <
      ENNReal.ofReal ((c0 / 4) * T) * volume V ^ (1 / 2 : ℝ) := by
  have hVle : volume V ≤ volume U := measure_mono hVU
  have hVfin : volume V ≠ ∞ := by
    intro h
    exact hUfin (le_antisymm le_top (le_trans (le_of_eq h.symm) hVle))
  have hto : v0 * (volume U).toReal ≤ (volume V).toReal := by
    have h1 := ENNReal.toReal_mono hVfin hvol
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hv0.le] at h1
  have hvpos : 0 < (volume V).toReal := by
    linarith [hto, mul_pos hv0 hUpos]
  have hsqrt : Real.sqrt v0 * Real.sqrt (volume U).toReal ≤ Real.sqrt (volume V).toReal := by
    rw [← Real.sqrt_mul hv0.le]
    exact Real.sqrt_le_sqrt hto
  have hnormr : (eLpNorm f 2 (volume.restrict U)).toReal ≤
      (c0 / 8) * T * Real.sqrt (volume V).toReal := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.toReal_eLpNorm_eq_sqrt_volume_mul_normalizedL2On
      hUpos hf]
    calc Real.sqrt (volume U).toReal * normalizedL2On U f ≤
        Real.sqrt (volume U).toReal * ((c0 / 8) * Real.sqrt v0 * T) :=
          mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg (volume U).toReal)
      _ = (c0 / 8) * T * (Real.sqrt v0 * Real.sqrt (volume U).toReal) := by ring
      _ ≤ (c0 / 8) * T * Real.sqrt (volume V).toReal :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hRHSfin : ENNReal.ofReal ((c0 / 4) * T) * volume V ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hVfin).ne
  have hRHSto : (ENNReal.ofReal ((c0 / 4) * T) * volume V ^ (1 / 2 : ℝ)).toReal =
      (c0 / 4) * T * Real.sqrt (volume V).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← ENNReal.toReal_rpow,
      ← Real.sqrt_eq_rpow]
  have hLHSfin : eLpNorm f 2 (volume.restrict U) ≠ ∞ := hf.2.ne
  have hstrict : (c0 / 8) * T * Real.sqrt (volume V).toReal <
      (c0 / 4) * T * Real.sqrt (volume V).toReal := by
    have h1 : (c0 / 8) * T < (c0 / 4) * T := by nlinarith [hc0, hT]
    exact mul_lt_mul_of_pos_right h1 (Real.sqrt_pos.2 hvpos)
  apply (ENNReal.toReal_lt_toReal hLHSfin hRHSfin).1
  rw [hRHSto]
  calc (eLpNorm f 2 (volume.restrict U)).toReal ≤ (c0 / 8) * T * Real.sqrt (volume V).toReal :=
      hnormr
    _ < (c0 / 4) * T * Real.sqrt (volume V).toReal := hstrict

/-- The chosen cap and contraction leave half the positive profile as a lower bound. -/
theorem goodCube_torsion_lower_budget
    {c0 K T : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hK : 1 ≤ K) (hT : 0 ≤ T) :
    (c0 / 2) * T ≤ c0 * T - (c0 / 4) * T -
      ((c0 / (8 * (K + 1))) * (K * T + 2 * ((c0 / 16) * T)) +
        2 * ((c0 / 16) * T)) := by
  have hden : (0 : ℝ) < 8 * (K + 1) := by nlinarith
  have key : (c0 / (8 * (K + 1))) * (K + c0 / 8) ≤ c0 / 8 := by
    have h1 : c0 * (K + c0 / 8) ≤ c0 * (K + 1) := by nlinarith
    calc c0 / (8 * (K + 1)) * (K + c0 / 8) = c0 * (K + c0 / 8) / (8 * (K + 1)) := by ring
      _ ≤ c0 * (K + 1) / (8 * (K + 1)) := div_le_div_of_nonneg_right h1 hden.le
      _ = c0 / 8 := by field_simp
  have h2 : 2 * ((c0 / 16) * T) = (c0 / 8) * T := by ring
  have h3 : (c0 / (8 * (K + 1))) * (K * T + (c0 / 8) * T) =
      (c0 / (8 * (K + 1))) * (K + c0 / 8) * T := by ring
  rw [h2, h3]
  nlinarith [key, mul_le_mul_of_nonneg_right key hT, hT, hc0]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
