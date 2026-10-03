module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.JBoundByBesov
public import SubdiffusiveProcess.Besov.ResponseByHattedNorm

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
def aux_l_J_bound_by_Besov_hHatNorm {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ⨆ φ : {φ : Vec d → Vec d // ContDiff ℝ ∞ φ},
    ENNReal.ofReal |∫ x, vecDot (F x) (φ.1 x) ∂normalizedCubeMeasure Q| /
      ENNReal.ofReal
        (Real.sqrt (∫ x, ∑ i : Fin d, ∑ j : Fin d,
            (fderiv ℝ φ.1 x (Pi.single j 1) i) ^ 2 ∂normalizedCubeMeasure Q) +
          (cubeScaleFactor Q)⁻¹ * Real.sqrt (∫ x, vecNormSq (φ.1 x) ∂normalizedCubeMeasure Q))



theorem l_J_bound_by_Besov {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ), 0 < m →
      ∀ (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a),
        (∀ x : Vec d, (a.toFun x).IsSymm) →
      ∀ (p q : Vec d)
        (v : Ch02.Solution (Ch02.cubeDomain (originCube d (m : ℤ)))
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
            (originCube d (m : ℤ)))),
        Ch02.IsResponseMaximizer (Ch02.cubeDomain (originCube d (m : ℤ)))
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
            (originCube d (m : ℤ))) p q v →
        Ch02.responseJ (Ch02.cubeDomain (originCube d ((m : ℤ) - 1)))
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
              (originCube d ((m : ℤ) - 1))) p q ≤
          C *
              Ch02.LambdaS (originCube d (m : ℤ)) (1 / 4)
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
              Real.sqrt
                (Ch02.LambdaS (originCube d (m : ℤ)) (1 / 4)
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) /
                  Ch02.lambdaS (originCube d (m : ℤ)) (1 / 4)
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)) *
              ((3 : ℝ) ^ (-2 * (m : ℤ)) *
                (aux_l_J_bound_by_Besov_hHatNorm (originCube d (m : ℤ)) v.toH1.grad).toReal ^ 2) +
            ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) 1,
              2 * (Ch02.responseJ (Ch02.cubeDomain R)
                      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) p q -
                    Ch02.responseJ (Ch02.cubeDomain (originCube d (m : ℤ)))
                      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                        (originCube d (m : ℤ))) p q) := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨1, by norm_num, ?_⟩
    intro m hm a ha hsym p q v hv
    have hJzero : ∀ Q : TriadicCube 0,
        Ch02.responseJ (Ch02.cubeDomain Q)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q = 0 := by
      intro Q
      rw [Ch02.responseJ_eq_coarseMatrices_formula_canonical]
      simp [vecDot]
    simp_rw [hJzero]
    have hn : aux_l_J_bound_by_Besov_hHatNorm (originCube 0 (m : ℤ)) v.toH1.grad = 0 := by
      simp [aux_l_J_bound_by_Besov_hHatNorm, vecDot]
    simp [hn]
  · letI : NeZero d := ⟨hd⟩
    obtain ⟨C, hC, hbound⟩ := SubdiffusiveProcess.Besov.exists_responseJ_centralChild_le_hHatNorm d
    refine ⟨C, hC, ?_⟩
    intro m hm a ha hsym p q v hv
    have h := hbound a ha (m : ℤ) p q
    have hgrad := SubdiffusiveProcess.Besov.maximizer_gradient_eq_canonical a ha
      (originCube d (m : ℤ)) p q v hv
    have hn : aux_l_J_bound_by_Besov_hHatNorm (originCube d (m : ℤ)) v.toH1.grad =
        SubdiffusiveProcess.Besov.hHatNorm (originCube d (m : ℤ))
          (SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.canonicalCubeMaximizerSolution a ha
            (originCube d (m : ℤ)) p q).toH1.grad := by
      change SubdiffusiveProcess.Besov.hHatNorm _ _ = _
      exact SubdiffusiveProcess.Besov.hHatNorm_congr_ae _ hgrad
    rw [← hn] at h
    exact h

end Paper
