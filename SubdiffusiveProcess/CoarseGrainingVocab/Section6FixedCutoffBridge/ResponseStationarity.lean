module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CoarseResponseMoments

@[expose] public section

/-!
# Uniform-in-cube moments of the coarse response

The union bound of `UnionBound.lean` needs a **single** moment bound valid for
every cube of the descendant family.  The coarse response is stationary: the
value on a triadic cube `Q` is the value on the centred cube of the same scale,
evaluated at the translated sample.  Since the potential law is translation
invariant, all moments agree.

Both matrix translation identities are already public
(`randomAMatrix_cube_eq_originCube_translate`,
`randomAStarInv_cube_eq_originCube_translate`), and `J` is an exact quadratic
form in the two matrices, so the response identity is immediate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

private abbrev S4 (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-- Stationarity of the coarse response across cubes of a fixed scale. -/
theorem cutoffResponseOnCube_cube_eq_originCube_translate
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (p q : Vec d)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    cutoffResponseOnCube M L p q Q omega =
      cutoffResponseOnCube M L p q (originCube d Q.scale)
        (translatePotentialSequence (triadicCubeShift Q) omega) := by
  have hQ : cutoffResponseOnCube M L p q Q omega =
      (1 / 2 : ℝ) * vecDot p
          (matVecMul (randomAMatrix M L (Ch02.cubeDomain Q) omega) p) +
        (1 / 2 : ℝ) * vecDot q
          (matVecMul ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹) q) -
        vecDot p q := by
    simpa [cutoffResponseOnCube, aCutoffFamily, aCutoffTriadicData] using!
      cutoffResponseJ_eq_randomMatrixQuadratics M L (Ch02.cubeDomain Q) p q omega
  have hO : cutoffResponseOnCube M L p q (originCube d Q.scale)
        (translatePotentialSequence (triadicCubeShift Q) omega) =
      (1 / 2 : ℝ) * vecDot p
          (matVecMul (randomAMatrix M L
            (Ch02.cubeDomain (originCube d Q.scale))
            (translatePotentialSequence (triadicCubeShift Q) omega)) p) +
        (1 / 2 : ℝ) * vecDot q
          (matVecMul ((randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d Q.scale))
            (translatePotentialSequence (triadicCubeShift Q) omega))⁻¹) q) -
        vecDot p q := by
    simpa [cutoffResponseOnCube, aCutoffFamily, aCutoffTriadicData] using!
      cutoffResponseJ_eq_randomMatrixQuadratics M L
        (Ch02.cubeDomain (originCube d Q.scale)) p q
        (translatePotentialSequence (triadicCubeShift Q) omega)
  rw [hQ, hO, randomAMatrix_cube_eq_originCube_translate M L omega Q,
    randomAStarInv_cube_eq_originCube_translate M L omega Q]

/-- **Uniform-in-cube moments.**  Every cube of a given scale carries the same
`xi`-th absolute moment of the coarse response as the centred cube. -/
theorem integral_abs_cutoffResponseOnCube_rpow_eq_originCube [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (p q : Vec d)
    (Q : TriadicCube d) (xi : ℝ) :
    (∫ omega, |cutoffResponseOnCube M L p q Q omega| ^ xi ∂M.P.toMeasure) =
      ∫ omega, |cutoffResponseOnCube M L p q
        (originCube d Q.scale) omega| ^ xi ∂M.P.toMeasure := by
  have hfun : (fun omega : S4 d =>
      |cutoffResponseOnCube M L p q Q omega| ^ xi) =
      fun omega : S4 d =>
        (fun eta : S4 d =>
          |cutoffResponseOnCube M L p q (originCube d Q.scale) eta| ^ xi)
          (translatePotentialSequence (triadicCubeShift Q) omega) := by
    funext omega
    rw [cutoffResponseOnCube_cube_eq_originCube_translate M L p q Q omega]
  rw [hfun]
  refine Homogenization.integral_comp_eq_of_map_eq
    (measurable_translatePotentialSequence (triadicCubeShift Q))
    (potentialSequenceLaw_stationary M (triadicCubeShift Q))
    (fun eta : S4 d =>
      |cutoffResponseOnCube M L p q (originCube d Q.scale) eta| ^ xi)
    ?_
  have habs : Measurable fun eta : S4 d =>
      |cutoffResponseOnCube M L p q (originCube d Q.scale) eta| := by
    simpa only [Real.norm_eq_abs] using
      (measurable_cutoffResponseOnCube M L p q (originCube d Q.scale)).norm
  exact (habs.pow_const xi).aestronglyMeasurable

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
