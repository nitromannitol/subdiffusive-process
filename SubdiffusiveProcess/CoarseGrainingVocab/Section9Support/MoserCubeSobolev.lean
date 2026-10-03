module

public import SubdiffusiveProcess.Section9.ShapeCubeGeometry
public import Homogenization.Sobolev.CubeEmbedding.LimitFiniteP
public import Homogenization.Sobolev.W1p.FiniteMeasureDowngrade

@[expose] public section

/-!
# A Sobolev gain valid in every dimension at least two

Use the source exponent `2d/(d+1) < 2` and its Sobolev conjugate
`2d/(d-1) > 2`. On cubes of side at most one, Hölder downgrades the
`H¹` data to the source exponent with factor at most one. In dimension
two the target exponent is exactly four. In higher dimensions this is
a subcritical gain, sufficient for Moser iteration with `chi = d/(d-1)`.
All constants are chosen before the cube, its scale, and the function.
-/

set_option autoImplicit false
noncomputable section

open Homogenization MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A common Sobolev target exponent for dimensions `d ≥ 2`. -/
def moserSobolevExponent (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))

/-- The chosen target strictly improves `L²`. -/
theorem two_lt_moserSobolevExponent {d : ℕ} (hd : 2 ≤ d) :
    2 < moserSobolevExponent d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [moserSobolevExponent, ENNReal.ofNat_lt_ofReal]
  apply (lt_div_iff₀ (by linarith : (0 : ℝ) < d - 1)).mpr
  linarith

@[simp] theorem moserSobolevExponent_two : moserSobolevExponent 2 = 4 := by
  norm_num [moserSobolevExponent]

private def moserSourceExponent (d : ℕ) (hd : 2 ≤ d) : FiniteLpExponent where
  exponent := ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1))
  one_lt := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [ENNReal.one_lt_ofReal]
    apply (lt_div_iff₀ (by linarith : (0 : ℝ) < d + 1)).mpr
    linarith
  lt_top := ENNReal.ofReal_lt_top

private theorem moserSourceExponent_toReal {d : ℕ} (hd : 2 ≤ d) :
    (moserSourceExponent d hd).exponent.toReal =
      2 * (d : ℝ) / ((d : ℝ) + 1) := by
  exact ENNReal.toReal_ofReal (by positivity)

private theorem moserSourceExponent_le_two {d : ℕ} (hd : 2 ≤ d) :
    (moserSourceExponent d hd).exponent ≤ 2 := by
  change ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1)) ≤ 2
  rw [ENNReal.ofReal_le_ofNat]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < d + 1)).mpr
  linarith

private theorem moserSourceExponent_lt_dim {d : ℕ} (hd : 2 ≤ d) :
    (moserSourceExponent d hd).exponent.toReal < d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [moserSourceExponent_toReal]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < d + 1)).mpr
  nlinarith

private def moserTargetExponent (d : ℕ) (hd : 2 ≤ d) : FiniteLpExponent where
  exponent := moserSobolevExponent d
  one_lt := lt_trans (by norm_num) (two_lt_moserSobolevExponent hd)
  lt_top := ENNReal.ofReal_lt_top

private theorem moser_exponent_relation {d : ℕ} (hd : 2 ≤ d) :
    (moserTargetExponent d hd).exponent.toReal⁻¹ =
      (moserSourceExponent d hd).exponent.toReal⁻¹ - (d : ℝ)⁻¹ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hm : (d : ℝ) - 1 ≠ 0 := by linarith
  have hp : (d : ℝ) + 1 ≠ 0 := by linarith
  rw [moserSourceExponent_toReal]
  change (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))).toReal⁻¹ = _
  rw [ENNReal.toReal_ofReal (div_nonneg (by positivity) (by linarith))]
  field_simp
  ring

private theorem eLpNorm_le_two_of_mass_le_one
    {α : Type*} [MeasurableSpace α] {mu : Measure α}
    (hm : mu Set.univ ≤ 1) (p : FiniteLpExponent) (hp : p.exponent ≤ 2)
    {f : α → ℝ} (hf : AEStronglyMeasurable f mu) :
    eLpNorm f p.exponent mu ≤ eLpNorm f 2 mu := by
  have hp0 : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne
  have hp2 : p.exponent.toReal ≤ 2 := by
    simpa only [ENNReal.toReal_ofNat] using
      ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hp
  have he : 0 ≤ 1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal := by
    norm_num only [ENNReal.toReal_ofNat]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hp0 hp2)
  have hfac : mu Set.univ ^ (1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal) ≤ 1 :=
    (ENNReal.rpow_le_rpow hm he).trans_eq (ENNReal.one_rpow _)
  exact (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf).trans
    ((mul_le_mul' le_rfl hfac).trans_eq (mul_one _))

/-- The subcritical Sobolev inequality with an `H¹` input, including `d = 2`. -/
theorem exists_moser_cube_sobolev {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (z : Vec d) (L : ℝ), 0 < L → L ≤ 1 →
      ∀ u : H1Function (axisCube z L),
        eLpNorm u.toFun (moserSobolevExponent d) (volume.restrict (axisCube z L)) ≤
          (C : ℝ≥0∞) *
            ((∑ i : Fin d, eLpNorm (fun x => u.grad x i) 2
                (volume.restrict (axisCube z L))) +
              ENNReal.ofReal L⁻¹ * eLpNorm u.toFun 2
                (volume.restrict (axisCube z L))) := by
  obtain ⟨C, hC, hSob⟩ := cubeSobolevEmbedding_finiteLp
    (show 0 < d by omega) (moserSourceExponent d hd) (moserSourceExponent_lt_dim hd)
  refine ⟨C, hC, ?_⟩
  intro z L hL hL1 u
  letI : IsFiniteMeasure (volume.restrict (axisCube z L)) :=
    (isOpenBoundedConvexDomain_axisCube z L).isFiniteMeasure_restrict_volume
  have hmass : (volume.restrict (axisCube z L)) Set.univ ≤ 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      axisCube, Real.volume_pi_Ioo]
    apply Finset.prod_le_one
    intro i _
    rw [add_sub_cancel_left]
    exact ENNReal.ofReal_le_one.mpr hL1
  have hdowngrade {f : Vec d → ℝ}
      (hf : AEStronglyMeasurable f (volume.restrict (axisCube z L))) :=
    eLpNorm_le_two_of_mass_le_one hmass (moserSourceExponent d hd)
      (moserSourceExponent_le_two hd) hf
  have hs := hSob (moserTargetExponent d hd) (moser_exponent_relation hd) z L hL
    (u.toW1pOfExponentLETwo (moserSourceExponent d hd) (moserSourceExponent_le_two hd))
  refine hs.trans (mul_le_mul' le_rfl (add_le_add ?_ ?_))
  · apply Finset.sum_le_sum
    intro i _
    exact hdowngrade (u.gradMemL2 i).aestronglyMeasurable
  · exact mul_le_mul' le_rfl (hdowngrade u.memL2.aestronglyMeasurable)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
