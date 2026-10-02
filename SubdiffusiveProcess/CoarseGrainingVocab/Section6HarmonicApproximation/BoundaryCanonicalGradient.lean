import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoercivePrices
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1

/-!
# Euclidean-gradient price of the local canonical cutoff

`LocalPatchCutoff` controls the Fréchet derivative in operator norm.  The
direct boundary test is written with the coordinate Euclidean gradient.  This
file records their finite-dimensional conversion once, including the exact
local gap scale.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization
open Homogenization.WeakPoissonEquationOn

noncomputable section

variable {d : ℕ}

theorem vecNormSq_euclideanGradient_coarseCaccioppoliLocalCanonicalFun_le
    (Q : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (x : Vec d) :
    vecNormSq (euclideanGradient
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x) ≤
      (d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          ((rhoOuter - rhoInner) * (cubeRadius Q / 3))) ^ 2 := by
  let K : ℝ := quantitativeCubeCutoffGradientConst d /
    ((rhoOuter - rhoInner) * (cubeRadius Q / 3))
  have hbase := vecNormSq_euclideanGradient_le_card_mul_fderiv_norm_sq
    (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x
  have hgrad : ‖fderiv ℝ
      (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x‖ ≤ K := by
    simpa only [K] using
      coarseCaccioppoliLocalCanonicalFun_gradient_bound
        Q center hinner hinnerOuter x
  have hK : 0 ≤ K := (norm_nonneg _).trans hgrad
  have hsq : ‖fderiv ℝ
      (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x‖ ^ 2 ≤
      K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgrad 2
  exact hbase.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg d))

theorem boundaryCoerciveCutoffDensity_localCanonicalFun_le
    (Q : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    {a w : Vec d → ℝ} {Lam : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    {x : Vec d} (ha0 : 0 ≤ a x) (haLam : a x ≤ Lam) :
    boundaryCoerciveCutoffDensity a
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) w x ≤
      Lam * ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          ((rhoOuter - rhoInner) * (cubeRadius Q / 3))) ^ 2) * w x ^ 2 := by
  exact boundaryCoerciveCutoffDensity_le_sq ha0 haLam
    (vecNormSq_euclideanGradient_coarseCaccioppoliLocalCanonicalFun_le
      Q center hinner hinnerOuter x)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
