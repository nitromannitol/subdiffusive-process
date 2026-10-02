import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicRatioSobolev
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserLocalBoundedness
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.Restriction

/-! # The positive-part Moser endpoint for bounded H¹ weak solutions

This version ends in an almost-everywhere bound and requires no continuous
representative. It is the analytic input for constructing that representative.
-/
set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The positive-part endpoint, with the dimensional constant chosen before all inputs. -/
theorem exists_essential_harmonic_positive_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (a : Vec d → ℝ) (z : Vec d),
        (∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), 1 / 4 ≤ a x ∧ a x ≤ 4) →
        AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
        ∀ u : H1Function (centeredAxisCube z 1), IsWeaklyHarmonicOn a (centeredAxisCube z 1) u →
        ∀ M : ℝ, 0 ≤ M →
        (∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), |u.toFun x| ≤ M) →
        ∀ᵐ x ∂volume.restrict (centeredAxisCube z (1 / 4)),
          ENNReal.ofReal (max (u.toFun x) 0) ≤
            ENNReal.ofReal B * eLpNorm (fun y => max (u.toFun y) 0) 2 (volume.restrict (centeredAxisCube z 1)) := by
  let chi : ℝ := (d : ℝ) / ((d : ℝ) - 1)
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 1 := by linarith
  have hchi : 1 < chi := by
    rw [show chi = (d : ℝ) / ((d : ℝ) - 1) from rfl, one_lt_div hden]
    linarith
  have hchi0 : 0 < chi := by linarith
  obtain ⟨C, hC, hstep⟩ := exists_harmonic_ratio_h1_power_sobolev_step hd
  obtain ⟨B, hB, hiter⟩ := exists_moser_iteration_constant hchi hC
  refine ⟨B, hB, ?_⟩
  intro a z hab ha u hu M hM hub
  let g : Vec d → ℝ := fun y => max (u.toFun y) 0
  let N : ℕ → ℝ≥0∞ := fun n => eLpNorm g (ENNReal.ofReal (2 * chi ^ n))
    (volume.restrict (centeredAxisCube z (moserIterationRadius n)))
  have hg0 (y : Vec d) : 0 ≤ g y := le_max_right _ _
  have hrec (n : ℕ) : N (n + 1) ^ (chi ^ n) ≤
      ENNReal.ofReal (8 * C * (2 * chi) ^ n) * N n ^ (chi ^ n) := by
    have hgap0 : 0 < moserIterationRadius n - moserIterationRadius (n + 1) := by
      rw [moserIterationRadius_gap]
      positivity
    have hrR := sub_pos.mp hgap0
    have hR1 : moserIterationRadius n ≤ 1 := (moserIterationRadius_bounds n).2.trans (by norm_num)
    have hsub := centeredAxisCube_mono (x := z) hR1
    have hs1 : 1 ≤ chi ^ n := one_le_pow₀ hchi.le
    have hImprove := hstep a z (moserIterationRadius (n + 1)) (moserIterationRadius n)
      (lt_trans (by norm_num) (moserIterationRadius_bounds (n + 1)).1) hrR hR1
      (ha.mono_measure (Measure.restrict_mono hsub le_rfl))
      (hab.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
      (u.restrict (isOpen_axisCube _ _) hsub)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.isWeaklyHarmonicOn_restrict
        (isOpen_axisCube _ _) (isOpen_axisCube _ _) hsub hu)
      M hM (hub.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))) (chi ^ n) hs1
    have hnormpow (p : ℝ≥0∞) (V : Set (Vec d)) :
        eLpNorm (fun y => (max (u.toFun y) 0) ^ (chi ^ n)) p (volume.restrict V) =
          eLpNorm g (p * ENNReal.ofReal (chi ^ n)) (volume.restrict V) ^ (chi ^ n) := by
      convert eLpNorm_norm_rpow (μ := volume.restrict V) (p := p) g (pow_pos hchi0 n) using 2
      ext y
      exact congrArg (fun t : ℝ => t ^ (chi ^ n)) (Real.norm_of_nonneg (hg0 y)).symm
    dsimp only [H1Function.restrict] at hImprove
    rw [hnormpow, hnormpow] at hImprove
    have hexp : moserSobolevExponent d * ENNReal.ofReal (chi ^ n) =
        ENNReal.ofReal (2 * chi ^ (n + 1)) := by
      rw [moserSobolevExponent, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (d : ℝ) / ((d : ℝ) - 1))]
      congr 1
      dsimp only [chi]
      rw [pow_succ]
      ring
    have hexp2 : (2 : ℝ≥0∞) * ENNReal.ofReal (chi ^ n) = ENNReal.ofReal (2 * chi ^ n) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hcoef : C * chi ^ n / (moserIterationRadius n - moserIterationRadius (n + 1)) =
        8 * C * (2 * chi) ^ n := by
      rw [moserIterationRadius_gap, one_div, div_inv_eq_mul, mul_pow]
      ring
    rw [hexp, hexp2, hcoef] at hImprove
    exact hImprove
  have hN := hiter N hrec
  have hN0 : N 0 ≤ eLpNorm (fun y => max (u.toFun y) 0) 2 (volume.restrict (centeredAxisCube z 1)) := by
    dsimp only [N]
    norm_num only [pow_zero, mul_one, ENNReal.ofReal_ofNat]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono
      (centeredAxisCube_mono ((moserIterationRadius_bounds 0).2.trans (by norm_num))) le_rfl)
  let K : ℝ≥0∞ := ENNReal.ofReal B * eLpNorm (fun y => max (u.toFun y) 0) 2 (volume.restrict (centeredAxisCube z 1))
  by_cases hKtop : K = ⊤
  · filter_upwards with x
    change ENNReal.ofReal (g x) ≤ K
    rw [hKtop]
    exact le_top
  have hbound (n : ℕ) : eLpNorm g (ENNReal.ofReal (2 * chi ^ n))
      (volume.restrict (centeredAxisCube z (1 / 4))) ≤ ENNReal.ofReal K.toReal := by
    rw [ENNReal.ofReal_toReal hKtop]
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono
      (centeredAxisCube_mono (moserIterationRadius_bounds n).1.le) le_rfl)).trans
      ((hN n).trans (mul_le_mul' le_rfl hN0))
  have hgmeas : AEStronglyMeasurable g (volume.restrict (centeredAxisCube z (1 / 4))) :=
    (u.memL2.1.sup (aestronglyMeasurable_const (b := (0 : ℝ)))).mono_measure
      (Measure.restrict_mono (centeredAxisCube_mono (by norm_num : (1 / 4 : ℝ) ≤ 1)) le_rfl)
  have hae := moser_ae_bound_of_eLpNorm_bounds
    hgmeas
    (fun n => mul_pos (by norm_num) (pow_pos hchi0 n))
    (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      (tendsto_pow_atTop_atTop_of_one_lt hchi)) ENNReal.toReal_nonneg hbound
  filter_upwards [hae] with x hx
  change ENNReal.ofReal (g x) ≤ K
  rw [← ENNReal.ofReal_toReal hKtop]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hx)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
