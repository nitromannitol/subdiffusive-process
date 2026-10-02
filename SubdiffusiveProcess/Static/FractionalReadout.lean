import SubdiffusiveProcess.Static.OverlapGap
import SubdiffusiveProcess.Besov.DetachMain
import Homogenization.Sobolev.Fractional.CongruenceAE

/-! # Fractional readout of the native negative Besov gradient norm

The exact overlap depth supremum is first proved finite. This prevents
using a real-valued norm's junk value when passing to the lower integral.
-/

open MeasureTheory Homogenization
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- On the unit cube the native `H¹` function has the normalized `L²`
membership used by the overlap comparison. -/
theorem H1Function_memLp_normalized_unit {d : ℕ}
    (H : H1Function (openCubeSet (originCube d 0))) :
    MemLp H.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) := by
  have hset : volume.restrict (cubeSet (originCube d 0)) =
      volume.restrict (openCubeSet (originCube d 0)) :=
    Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet _)
  unfold normalizedCubeMeasure cubeMeasure
  rw [hset]
  exact H.memL2.smul_measure ENNReal.ofReal_ne_top

/-- The exact depth supremum is finite for each native `H¹` function. -/
theorem exactOverlap_depth_iSup_lt_top {d : ℕ} [NeZero d]
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (H : H1Function (openCubeSet (originCube d 0)))
    (hu : ExactOverlapIntegrable (originCube d 0) H.toFun) :
    (iSup fun j : ℕ => exactOverlapDepthTerm
      (originCube d 0) (1 - s) 2 H.toFun hu j) < ⊤ := by
  let R : ℝ := 2 * Besov.Detach.Cd d * s *
    ∑' m : ℕ, (3 : ℝ) ^ (-s * (m : ℝ)) * Besov.Detach.gradX H m
  refine lt_of_le_of_lt (b := ENNReal.ofReal R) (iSup_le fun j => ?_) ENNReal.ofReal_lt_top
  rw [Besov.Detach.exactDepthTerm_eq]
  exact ENNReal.ofReal_le_ofReal (Besov.Detach.depth_term_le s hs.1 hs.2 H j)

/-- The squared `W^{3/4,2}` seminorm on the unit cube is controlled by the
squared `B^{-1/16}_{2,1}` norm of the gradient, with a dimensional constant.
The statement is ENNReal-valued, including genuine finiteness. -/
theorem exists_unit_fractional_readout (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : H1Function (openCubeSet (originCube d 0)), Measurable H.toFun →
        Gagliardo.cubeGagliardoESeminorm (originCube d 0) (3 / 4) 2 H.toFun ^ 2 ≤
          ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
            (originCube d 0) (1 / 16) (.finite 1) H.grad ^ 2) := by
  obtain ⟨D, hD, hdetach⟩ := Besov.Detach.detach_main d
  let N : ℝ := 2 ^ 3 * 3 ^ (3 * d + 2)
  let gap : ℝ := 1 - (3 : ℝ) ^ (-2 * ((1 / 4 : ℝ) - 1 / 16))
  have hN : 0 < N := by dsimp only [N]; positivity
  have hgap : 0 < gap := by
    dsimp only [gap]
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (3 : ℝ))
      (by norm_num : -2 * ((1 / 4 : ℝ) - 1 / 16) < 0)
    linarith
  refine ⟨N ^ 2 * D ^ 2 / gap, by positivity, ?_⟩
  intro H hmeas
  have hmem := H1Function_memLp_normalized_unit H
  let hu : ExactOverlapIntegrable (originCube d 0) H.toFun :=
    exactDualOverlapIntegrable (originCube d 0) 2 (by norm_num) (by simpa using hmem)
  let T : ℝ≥0∞ := iSup fun j : ℕ => exactOverlapDepthTerm
    (originCube d 0) (1 - 1 / 16) 2 H.toFun hu j
  have hT : T < ⊤ := exactOverlap_depth_iSup_lt_top (1 / 16) (by norm_num) H hu
  have htbound := hdetach (1 / 16) (by norm_num) H hu
  have hnorm : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
      (originCube d 0) (1 / 16) (.finite 1) H.grad := by
    have hTnonneg : 0 ≤ T.toReal := ENNReal.toReal_nonneg
    dsimp only [T] at hTnonneg
    nlinarith only [htbound, hTnonneg, hD]
  have hsquare : T.toReal ^ 2 ≤ D ^ 2 *
      SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
        (originCube d 0) (1 / 16) (.finite 1) H.grad ^ 2 := by
    have hp := pow_le_pow_left₀ ENNReal.toReal_nonneg htbound 2
    simpa only [mul_pow] using hp
  have hgapbound := exactOverlap_gap_bound d (1 / 16) (by norm_num)
    H.toFun hu hmem hT
  have hgagliardo := gagliardo_sq_le_exactOverlapScalarSeminormTwo
    (⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1)
    (originCube d 0) H.toFun hu hmeas hmem
  have hconst : (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) =
      ENNReal.ofReal (N ^ 2) := by
    rw [ENNReal.rpow_two]
    rw [ENNReal.ofReal_pow hN.le]
    congr 1
    dsimp only [Gagliardo.gagliardoBesovLowerConstant, N]
    norm_cast
  refine hgagliardo.trans ?_
  rw [hconst]
  calc
    ENNReal.ofReal (N ^ 2) *
        (exactOverlapFiniteSeminorm (exactOverlapScalarTwoParameters
          (⟨3 / 4, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ) 1))
          (originCube d 0) H.toFun hu) ^ 2 ≤
        ENNReal.ofReal (N ^ 2) * ENNReal.ofReal (T.toReal ^ 2 / gap) :=
      mul_le_mul_left' hgapbound _
    _ = ENNReal.ofReal (N ^ 2 * (T.toReal ^ 2 / gap)) := by
      rw [ENNReal.ofReal_mul (sq_nonneg N)]
    _ ≤ ENNReal.ofReal ((N ^ 2 * D ^ 2 / gap) *
        SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          (originCube d 0) (1 / 16) (.finite 1) H.grad ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        N ^ 2 * (T.toReal ^ 2 / gap) ≤ N ^ 2 * ((D ^ 2 *
            SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
              (originCube d 0) (1 / 16) (.finite 1) H.grad ^ 2) / gap) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsquare hgap.le)
            (sq_nonneg N)
        _ = _ := by ring

/-- A measurable value representative preserves the original weak gradient. -/
theorem exists_measurable_H1Function {d : ℕ} {U : Set (Vec d)} (H : H1Function U) :
    ∃ H' : H1Function U, Measurable H'.toFun ∧ H'.grad = H.grad ∧
      H.toFun =ᵐ[volume.restrict U] H'.toFun := by
  let f := H.memL2.aestronglyMeasurable.mk H.toFun
  have hf : Measurable f := H.memL2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have heq : H.toFun =ᵐ[volume.restrict U] f := H.memL2.aestronglyMeasurable.ae_eq_mk
  let H' : H1Function U :=
    { toFun := f
      grad := H.grad
      memL2 := (memLp_congr_ae heq).mp H.memL2
      gradMemL2 := H.gradMemL2
      hasWeakGradient := by
        intro i φ hφ hφc hφs
        have hint : ∫ x in U, f x * (fderiv ℝ φ x) (basisVec i) =
            ∫ x in U, H.toFun x * (fderiv ℝ φ x) (basisVec i) := by
          apply integral_congr_ae
          filter_upwards [heq] with x hx
          rw [hx]
        rw [hint]
        exact H.hasWeakGradient i φ hφ hφc hφs }
  exact ⟨H', hf, rfl, heq⟩

/-- The fractional readout for all native `H¹` representatives. -/
theorem exists_unit_fractional_readout_all (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : H1Function (openCubeSet (originCube d 0)),
        Gagliardo.cubeGagliardoESeminorm (originCube d 0) (3 / 4) 2 H.toFun ^ 2 ≤
          ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
            (originCube d 0) (1 / 16) (.finite 1) H.grad ^ 2) := by
  obtain ⟨C, hC, hread⟩ := exists_unit_fractional_readout d
  refine ⟨C, hC, ?_⟩
  intro H
  obtain ⟨H', hmeas, hgrad, heq⟩ := exists_measurable_H1Function H
  have hcube : H.toFun =ᵐ[cubeMeasure (originCube d 0)] H'.toFun := by
    unfold cubeMeasure
    rw [Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet _)]
    exact heq
  rw [Gagliardo.cubeGagliardoESeminorm_congr_ae hcube]
  simpa only [hgrad] using hread H' hmeas

end SubdiffusiveProcess.Static
