module

public import SubdiffusiveProcess.Besov.Necas
public import SubdiffusiveProcess.Besov.SymmetricCoefficients

@[expose] public section

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators ENNReal ContDiff
noncomputable section
variable {d : ℕ} [NeZero d]

theorem centralChild_originCube_eq (m : ℤ) :
    CubeCalderonZygmund.centralChild (originCube d m) = originCube d (m - 1) := by
  apply congrArg₂ TriadicCube.mk
  · rfl
  · funext i
    simp [originCube]

theorem rpow_three_neg_two_scale_eq_zpow (m : ℤ) :
    Real.rpow (3 : ℝ) (-2 * (((originCube d m).scale : ℤ) : ℝ)) =
      (3 : ℝ) ^ (-2 * m) := by
  change Real.rpow (3 : ℝ) (-2 * (m : ℝ)) = _
  rw [show (-2 * (m : ℝ)) = ((-2 * m : ℤ) : ℝ) by push_cast; ring]
  exact Real.rpow_intCast 3 (-2 * m)

/-- The parent oscillation term is controlled by the paper's literal hatted norm. -/
theorem interiorCaccioppoliParentOscillationL2Sq_le_hHatNorm (m : ℤ)
    (a : CoeffFamily d) (v : CubeSolution (originCube d m) a) :
    interiorCaccioppoliParentOscillationL2Sq (originCube d m) a v ≤
      (neumannGradientTestConstant d ^ 2 + 1) *
        (hHatNorm (originCube d m) v.toH1.grad).toReal ^ 2 := by
  have heq : interiorCaccioppoliParentOscillationL2Sq (originCube d m) a v =
      cubeBesovOscillation (originCube d m) 2 v.toH1.toFun ^ 2 :=
    normalizedL2SqOnSet_openCubeSet_centred_eq_cubeBesovOscillation_sq (originCube d m) v.toH1
  rw [heq]
  have hs := pow_le_pow_left₀ (cubeBesovOscillation_nonneg _ _ _)
    (cube_oscillation_le_hHatNorm m v.toH1) 2
  nlinarith [sq_nonneg (hHatNorm (originCube d m) v.toH1.grad).toReal]

/-- Response on the central child, with the exact depth-one defect sum. -/
theorem exists_responseJ_centralChild_le_hHatNorm (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : RegCoeffField d)
      (ha : Ch04.AELocallyUniformlyEllipticField a) (m : ℤ) (p q : Vec d),
      Ch02.responseJ (Ch02.cubeDomain (originCube d (m - 1)))
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
            (originCube d (m - 1))) p q ≤
        C * Ch02.LambdaS (originCube d m) (1 / 4)
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
          Real.sqrt (Ch02.LambdaS (originCube d m) (1 / 4)
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) /
            Ch02.lambdaS (originCube d m) (1 / 4)
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)) *
          ((3 : ℝ) ^ (-2 * m) * (hHatNorm (originCube d m)
            (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad).toReal ^ 2) +
        ∑ R ∈ descendantsAtDepth (originCube d m) 1,
          2 * (Ch02.responseJ (Ch02.cubeDomain R)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) p q -
            Ch02.responseJ (Ch02.cubeDomain (originCube d m))
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                (originCube d m)) p q) := by
  obtain ⟨C₀, hC₀, hcacc⟩ := centralChildCaccioppoli_canonicalMaximizer d
  let B : ℝ := neumannGradientTestConstant d ^ 2 + 1
  let E : ℝ := jBesovCaccioppoliEnvelope C₀
  have hB : 0 < B := by dsimp [B]; positivity
  have hE : 0 < E := jBesovCaccioppoliEnvelope_pos C₀
  refine ⟨E * B, mul_pos hE hB, ?_⟩
  intro a ha m p q
  let Q := originCube d m
  let fam := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let v := canonicalCubeMaximizerSolution a ha Q p q
  have hΛ : 0 ≤ Ch02.LambdaS Q (1 / 4) fam :=
    Ch02.LambdaSq_finite_nonneg Q fam (by norm_num) le_rfl
  have hP : 0 ≤ caccioppoliPrefactor C₀ Q fam (1 / 4) (1 / 4) :=
    caccioppoliPrefactor_nonneg hC₀.le (by norm_num) (by norm_num) (by norm_num)
  have hosc := interiorCaccioppoliParentOscillationL2Sq_le_hHatNorm m fam v
  have hpref := caccioppoliPrefactor_diag_le_jBesovEnvelope C₀ hC₀.le Q fam
    (s := (1 / 4 : ℝ)) (by norm_num) le_rfl
  norm_num only at hpref
  have hsqrt : Real.rpow (Ch02.ThetaRatio Q (1 / 4) (1 / 4) fam) (1 / 2) =
      Real.sqrt (Ch02.ThetaRatio Q (1 / 4) (1 / 4) fam) := (Real.sqrt_eq_rpow _).symm
  have hz : Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) = (3 : ℝ) ^ (-2 * m) :=
    rpow_three_neg_two_scale_eq_zpow m
  rw [hsqrt, Ch02.ThetaRatio, hz] at hpref
  have hc := hcacc a ha Q p q (s := (1 / 4 : ℝ)) (t := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  rw [interiorCaccioppoliRHS] at hc
  have henergy : centralChildCaccioppoliEnergy Q fam v ≤
      (E * B) * Ch02.LambdaS Q (1 / 4) fam *
        Real.sqrt (Ch02.LambdaS Q (1 / 4) fam / Ch02.lambdaS Q (1 / 4) fam) *
        ((3 : ℝ) ^ (-2 * m) * (hHatNorm Q v.toH1.grad).toReal ^ 2) := by
    calc
      _ ≤ caccioppoliPrefactor C₀ Q fam (1 / 4) (1 / 4) *
          interiorCaccioppoliParentOscillationL2Sq Q fam v := hc
      _ ≤ caccioppoliPrefactor C₀ Q fam (1 / 4) (1 / 4) *
          (B * (hHatNorm Q v.toH1.grad).toReal ^ 2) :=
        mul_le_mul_of_nonneg_left hosc hP
      _ ≤ (E * (Real.sqrt (Ch02.LambdaS Q (1 / 4) fam / Ch02.lambdaS Q (1 / 4) fam) *
          Ch02.LambdaS Q (1 / 4) fam * (3 : ℝ) ^ (-2 * m))) *
          (B * (hHatNorm Q v.toH1.grad).toReal ^ 2) :=
        mul_le_mul_of_nonneg_right hpref (mul_nonneg hB.le (sq_nonneg _))
      _ = _ := by ring
  have hJ := responseJ_centralChild_le_centralChildCaccioppoliEnergy_add_defectSum a ha Q p q
  rw [centralChild_originCube_eq m] at hJ
  exact hJ.trans (add_le_add henergy le_rfl)

end
end SubdiffusiveProcess.Besov
