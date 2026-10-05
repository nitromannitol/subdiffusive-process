module

public import SubdiffusiveProcess.Static.UnitFractionalKernel
public import SubdiffusiveProcess.Besov.KilledMain

@[expose] public section

/-! # The trace-zero `L²` readout at the same coarse exponent -/

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- On the unit cube the endpoint negative norm is bounded by the smaller
exponent `1/16`, with the exact normalization factor `16`. -/
theorem unit_negativeBesov_one_le {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) :
    paperScaleNormalizedNegativeBesovVectorNorm (originCube d 0) 1 (.finite 1) H.grad ≤
      16 * paperScaleNormalizedNegativeBesovVectorNorm
        (originCube d 0) (1 / 16) (.finite 1) H.grad := by
  obtain ⟨G, hG⟩ := Besov.Detach.gradX_bdd H
  have hsummable := Besov.Detach.summable_weighted (1 / 16) (by norm_num)
    (Besov.Detach.gradX H) (Besov.Detach.gradX_nonneg H) G hG
  have hnn : ∀ m : ℕ, 0 ≤ (3 : ℝ) ^ (-(1 / 16) * (m : ℝ)) * Besov.Detach.gradX H m :=
    fun m => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Besov.Detach.gradX_nonneg H m)
  have hbdd : BddAbove (Set.range fun N : ℕ =>
      ∑ m ∈ Finset.range (N + 1),
        (3 : ℝ) ^ (-(1 / 16) * (m : ℝ)) * Besov.Detach.gradX H m) := by
    refine ⟨∑' m : ℕ, (3 : ℝ) ^ (-(1 / 16) * (m : ℝ)) * Besov.Detach.gradX H m, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact hsummable.sum_le_tsum _ (fun m _ => hnn m)
  have hsup :
      sSup (Set.range fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
        (3 : ℝ) ^ (-1 * (m : ℝ)) * Besov.Detach.gradX H m) ≤
      sSup (Set.range fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
        (3 : ℝ) ^ (-(1 / 16) * (m : ℝ)) * Besov.Detach.gradX H m) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨N, rfl⟩
    refine le_trans (Finset.sum_le_sum fun m _ => ?_) (le_csSup hbdd ⟨N, rfl⟩)
    apply mul_le_mul_of_nonneg_right _ (Besov.Detach.gradX_nonneg H m)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ))
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [Besov.Detach.paperNorm_eq, Besov.Detach.paperNorm_eq]
  convert hsup using 1 <;> ring

/-- The literal `L²` lower integral for trace-zero functions is bounded by
this same squared negative gradient norm. -/
theorem exists_unit_killed_readout (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : H10Function (openCubeSet (originCube d 0)),
        (∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (H.toFun x ^ 2)) ≤
          ENNReal.ofReal (C * paperScaleNormalizedNegativeBesovVectorNorm
            (originCube d 0) (1 / 16) (.finite 1) H.grad ^ 2) := by
  obtain ⟨K, hK, hkilled⟩ := Besov.Detach.killed_endpoint_main (d := d)
  refine ⟨(16 * K) ^ 2, by positivity, ?_⟩
  intro H
  have hunit : normalizedCubeMeasure (originCube d 0) =
      volume.restrict (openCubeSet (originCube d 0)) := by
    simp only [normalizedCubeMeasure, cubeVolume, cubeScaleFactor, originCube,
      zpow_zero, one_pow, inv_one, ENNReal.ofReal_one, one_smul]
    exact Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet _)
  have hle := (hkilled H).trans (mul_le_mul_of_nonneg_left
    (unit_negativeBesov_one_le H.toH1Function) hK.le)
  have hLp : 0 ≤ cubeLpNorm (originCube d 0) 2 H.toFun := ENNReal.toReal_nonneg
  have hsq := pow_le_pow_left₀ hLp hle 2
  have hnormTop := (H1Function_memLp_normalized_unit H.toH1Function).eLpNorm_ne_top
  have hENN : eLpNorm H.toFun 2 (normalizedCubeMeasure (originCube d 0)) ^ 2 =
      ENNReal.ofReal (cubeLpNorm (originCube d 0) 2 H.toFun ^ 2) := by
    unfold cubeLpNorm
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hnormTop]
  rw [← eLpNorm_two_sq_eq_lintegral_sq_of_aestronglyMeasurable _ _
    H.toH1Function.memL2.aestronglyMeasurable, ← hunit, hENN]
  apply ENNReal.ofReal_le_ofReal
  convert hsq using 1 ; ring

end SubdiffusiveProcess.Static
