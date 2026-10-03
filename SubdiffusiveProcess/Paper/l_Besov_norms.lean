module

public import SubdiffusiveProcess.Besov.FullNormEstimate
public import SubdiffusiveProcess.Besov.PaperCarriers

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- `‖F‖_{Ĥ^{-1}(Q)}` for a vector field `F` on the triadic cube `Q`: the case `s = 1` of the paper's inhomogeneous
negative Sobolev norm `(e.hatted.negative.norm.convention)`,
`sup_{φ ∈ C^∞(Q̄;ℝ^d), φ ≠ 0} |⨍_Q F·φ| / ([φ]_{H̲¹(Q)} + |Q|^{-1/d} ‖φ‖_{L̲²(Q)})`,
with `[φ]_{H̲¹(Q)} = ‖∇φ‖_{L̲²(Q)}` (Frobenius norm of the gradient matrix; the operator-norm reading changes the norm
by a factor depending only on `d`), test fields the globally smooth fields (restrictions of which are `C^∞(Q̄)`),
and the convention `0/0 = 0` for `φ = 0`. -/
def aux_l_Besov_norms_hHatNorm {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ⨆ φ : {φ : Vec d → Vec d // ContDiff ℝ ∞ φ},
    ENNReal.ofReal |∫ x, vecDot (F x) (φ.1 x) ∂normalizedCubeMeasure Q| /
      ENNReal.ofReal
        (Real.sqrt (∫ x, ∑ i : Fin d, ∑ j : Fin d,
            (fderiv ℝ φ.1 x (Pi.single j 1) i) ^ 2 ∂normalizedCubeMeasure Q) +
          (cubeScaleFactor Q)⁻¹ * Real.sqrt (∫ x, vecNormSq (φ.1 x) ∂normalizedCubeMeasure Q))



theorem l_Besov_norms {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ), 0 < m →
      ∀ (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a),
        (∀ x : Vec d, (a.toFun x).IsSymm) →
      ∀ (s : ℝ), 0 < s → s < 1 →
      ∀ (L0 : ℤ), L0 ≤ (m : ℤ) →
      ∀ (p q : Vec d)
        (v : Ch02.Solution (Ch02.cubeDomain (originCube d (m : ℤ)))
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
            (originCube d (m : ℤ)))),
        Ch02.IsResponseMaximizer (Ch02.cubeDomain (originCube d (m : ℤ)))
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
            (originCube d (m : ℤ))) p q v →
        (3 : ℝ) ^ (-(m : ℤ)) *
            (aux_l_Besov_norms_hHatNorm (originCube d (m : ℤ))
              (fun x => v.toH1.grad x -
                (matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain (originCube d (m : ℤ)))
                    ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                      (originCube d (m : ℤ)))) q - p))).toReal ≤
          C * Real.sqrt ((Ch02.lambdaS (originCube d (m : ℤ)) s
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))⁻¹) *
              ∑ k ∈ Finset.Icc L0 (m : ℤ),
                (3 : ℝ) ^ (-(1 - s) * (((m : ℤ) - k : ℤ) : ℝ)) *
                  Real.sqrt
                    ((((descendantsAtScale (originCube d (m : ℤ)) k).card : ℝ)⁻¹ *
                        ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) k,
                          Ch02.responseJ (Ch02.cubeDomain R)
                            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)
                            p q) -
                      Ch02.responseJ (Ch02.cubeDomain (originCube d (m : ℤ)))
                        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                          (originCube d (m : ℤ))) p q) +
            C * ∑ n ∈ Finset.Icc L0 (m : ℤ),
                (3 : ℝ) ^ (-(((m : ℤ) - n : ℤ) : ℝ)) *
                  Real.sqrt
                    (((descendantsAtScale (originCube d (m : ℤ)) n).card : ℝ)⁻¹ *
                      ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) n,
                        vecNormSq (matVecMul
                          (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain (originCube d (m : ℤ)))
                              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                                (originCube d (m : ℤ))) -
                            Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R)
                              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R))
                          q)) +
            C * Real.sqrt ((Ch02.lambdaS (originCube d (m : ℤ)) s
                  (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))⁻¹) / (1 - s) *
              (3 : ℝ) ^ (-(1 - s) * (((m : ℤ) - L0 : ℤ) : ℝ)) *
              Real.sqrt (cubeAverage (originCube d (m : ℤ))
                (fun x => vecDot (v.toH1.grad x) (matVecMul (a.toFun x) (v.toH1.grad x)))) +
            C * (3 : ℝ) ^ (-(((m : ℤ) - L0 : ℤ) : ℝ)) *
              Real.sqrt (vecNormSq
                (matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain (originCube d (m : ℤ)))
                    ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                      (originCube d (m : ℤ)))) q - p)) := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨1, by norm_num, ?_⟩
    intro m hm a ha hsym s hs hs1 L0 hLm p q v hv
    have hn : aux_l_Besov_norms_hHatNorm (originCube 0 (m : ℤ))
        (fun x => v.toH1.grad x -
          (matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain (originCube 0 (m : ℤ)))
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
              (originCube 0 (m : ℤ)))) q - p)) = 0 := by
      simp [aux_l_Besov_norms_hHatNorm, vecDot]
    rw [hn, ENNReal.toReal_zero, mul_zero]
    have hsden : 0 < 1 - s := by linarith
    positivity
  · letI : NeZero d := ⟨hd⟩
    let C : ℝ := 4 * (SubdiffusiveProcess.Besov.hHatBesovConstant d * (d : ℝ)) + 1
    have hC : 0 < C := by
      have h := SubdiffusiveProcess.Besov.hHatBesovConstant_pos d
      have hdreal : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      dsimp [C]
      nlinarith [mul_nonneg h.le hdreal]
    refine ⟨C, hC, ?_⟩
    intro m hm a ha hsym s hs hs1 L0 hLm p q v hv
    let Q : TriadicCube d := originCube d (m : ℤ)
    have hgrad := SubdiffusiveProcess.Besov.maximizer_gradient_eq_canonical a ha Q p q v hv
    have hn : aux_l_Besov_norms_hHatNorm Q
        (fun x => v.toH1.grad x -
          (matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)) q - p)) =
        SubdiffusiveProcess.Besov.hHatNorm Q
          (SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.maximizerGradientDefect a ha Q p q) := by
      change SubdiffusiveProcess.Besov.hHatNorm Q _ = _
      apply SubdiffusiveProcess.Besov.hHatNorm_congr_ae
      filter_upwards [hgrad] with x hx
      simp only [SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.maximizerGradientDefect,
        SubdiffusiveProcess.Besov.coarseScaleSeparation_eq_symmetric a ha hsym]
      exact congrArg (fun g => g -
        (matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)) q - p)) hx
    have h := SubdiffusiveProcess.Besov.scaled_hHatNorm_maximizerGradientDefect_le_fourTerm_full
      a ha hLm hs hs1 (r := Ch02.MultiscaleExponent.finite 1) (by norm_num) p q
    rw [← hn] at h
    simp only [SubdiffusiveProcess.Besov.lambdaSqCoeffField_one_eq a ha,
      SubdiffusiveProcess.Besov.coarseScaleSeparation_eq_symmetric a ha hsym,
      SubdiffusiveProcess.Besov.maximizerEnergyL2Norm_eq_paper a ha (originCube d (m : ℤ)) p q v hv] at h
    dsimp only [C]
    convert h using 1
    congr 3
    · congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [SubdiffusiveProcess.Besov.responseDefectAverageAtScale_eq_paper a ha
        (Finset.mem_Icc.mp hk).2 p q]
    · congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [SubdiffusiveProcess.Besov.coarseVariationAverage_eq_paper a ha hsym
        (Finset.mem_Icc.mp hk).2 p q]

end Paper
