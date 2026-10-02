import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryForcedRestriction
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryGoodEventAbsorption
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryArbitraryH1Circ
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Localization

/-!
# Descendant ellipticity prices for the boundary cover

The good event controls the multiscale coefficient constants on the parent
comparison cube.  The public Chapter 2 localization theorem transports those
constants to every cell of the finite descendant cover.  This is the
coefficient step used before the finite-cell corrected-flux summation.

PROVENANCE: mirrors the coefficient localization preceding the local patch
summation in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryOuterCaccioppoli.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Public finite-`q` upper ellipticity localizes from a cube to a descendant
at depth `j`, with the literal geometric loss. -/
theorem descendant_LambdaSq_finite_le_parent_of_mem_descendantsAtDepth
    {Q R : TriadicCube d} (A : Ch02.TriadicCoeffFamily d)
    {t q : ℝ} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (ht : 0 < t) (hq : 1 ≤ q) :
    Ch02.LambdaSq R t (.finite q) A ≤
      Real.rpow (3 : ℝ) (2 * t * (j : ℝ)) *
        Ch02.LambdaSq Q t (.finite q) A := by
  have hscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have hraw := Ch02.descendant_LambdaSq_finite_le
    (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) A hscale ht hq
  simpa [Ch02.multiscaleDescendantWeight] using hraw

/-- Public finite-`q` lower ellipticity localizes from a cube to a descendant
at depth `j`, in inverse form. -/
theorem descendant_lambdaSq_finite_inv_le_parent_of_mem_descendantsAtDepth
    {Q R : TriadicCube d} (A : Ch02.TriadicCoeffFamily d)
    {t q : ℝ} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (ht : 0 < t) (hq : 1 ≤ q) :
    (Ch02.lambdaSq R t (.finite q) A)⁻¹ ≤
      Real.rpow (3 : ℝ) (2 * t * (j : ℝ)) *
        (Ch02.lambdaSq Q t (.finite q) A)⁻¹ := by
  have hscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have hraw := Ch02.descendant_lambdaSq_finite_inv_le
    (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) A hscale ht hq
  simpa [Ch02.multiscaleDescendantWeight] using hraw

/-- A weighted pair of parent finite-`2` caps gives the corresponding pair
on every descendant.  The common depth loss is left explicit. -/
theorem descendant_sixth_caps_of_parent
    {Q R : TriadicCube d} (A : Ch02.TriadicCoeffFamily d)
    {s sigma K : ℝ} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (hs : 0 < s)
    (hsigma : 0 < sigma)
    (hupper : sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ K)
    (hlower : sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ K) :
    sigma⁻¹ * Ch02.LambdaSq R (s / 6) (.finite 2) A ≤
        Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ)) * K ∧
      sigma * (Ch02.lambdaSq R (s / 6) (.finite 2) A)⁻¹ ≤
        Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ)) * K := by
  let W : ℝ := Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ))
  have hW : 0 ≤ W := Real.rpow_nonneg (by norm_num) _
  have hL := descendant_LambdaSq_finite_le_parent_of_mem_descendantsAtDepth
    A hR (by linarith only [hs] : 0 < s / 6) (by norm_num : (1 : ℝ) ≤ 2)
  have hl := descendant_lambdaSq_finite_inv_le_parent_of_mem_descendantsAtDepth
    A hR (by linarith only [hs] : 0 < s / 6) (by norm_num : (1 : ℝ) ≤ 2)
  constructor
  · calc
      sigma⁻¹ * Ch02.LambdaSq R (s / 6) (.finite 2) A
          ≤ sigma⁻¹ * (W * Ch02.LambdaSq Q (s / 6) (.finite 2) A) :=
            mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr hsigma.le)
      _ = W * (sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A) := by ring
      _ ≤ W * K := mul_le_mul_of_nonneg_left hupper hW
  · calc
      sigma * (Ch02.lambdaSq R (s / 6) (.finite 2) A)⁻¹
          ≤ sigma * (W * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹) :=
            mul_le_mul_of_nonneg_left hl hsigma.le
      _ = W * (sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹) := by ring
      _ ≤ W * K := mul_le_mul_of_nonneg_left hlower hW

/-- The descendant weak-flux RHS is priced directly by the parent pair of
finite-`2` caps.  This is the analytic coefficient input for every active
cell in the adaptive summation. -/
theorem weakFluxWithRHSRHS_descendant_le_of_parent_sixth_caps
    {Q R : TriadicCube d} {A : CoeffFamily d}
    {C s sigma K G : ℝ} {j : ℕ} {g : Vec d → Vec d}
    (u : ForcedCubeSolution R A g)
    (hR : R ∈ descendantsAtDepth Q j)
    (hC : 0 ≤ C) (hs : 0 < s) (hsigma : 0 < sigma) (hK : 0 ≤ K)
    (hupper : sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ K)
    (hlower : sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ K)
    (hg : ForceBesovRegularity R (s / 3) g)
    (hG : scaleNormalizedPositiveBesovVectorSeminormTwo R (s / 3) g ≤ G) :
    let W : ℝ := Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ))
    weakFluxWithRHSRHS C R A (s / 3) g u ≤
      C * (s / 3)⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma) *
          forcedSolutionEnergyNorm R A u +
        C * Real.rpow (s / 3) (-(5 / 2 : ℝ)) *
          (Real.sqrt (W * K) * Real.sqrt sigma) *
          (Real.sqrt (W * K) * Real.sqrt sigma⁻¹) * G := by
  dsimp only
  obtain ⟨hupperR, hlowerR⟩ := descendant_sixth_caps_of_parent
    A hR hs hsigma hupper hlower
  exact weakFluxWithRHSRHS_le_of_sixth_caps u hC hs hsigma
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hK)
      hupperR hlowerR hg hG

/-- The parent lower finite-`2` cap also prices the public `q=1` lower
ellipticity slot on a descendant. -/
theorem descendant_lambdaS_inv_le_of_parent_sixth_cap
    {Q R : TriadicCube d} (A : CoeffFamily d)
    {s sigma K : ℝ} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (hs : 0 < s)
    (hsigma : 0 < sigma)
    (hlower : sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ K) :
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ))
    (Ch02.lambdaS R (s / 3) A)⁻¹ ≤ (W * K) * sigma⁻¹ := by
  dsimp only
  have hloc :=
    descendant_lambdaSq_finite_inv_le_parent_of_mem_descendantsAtDepth
      A hR (by linarith only [hs] : 0 < s / 6) (by norm_num : (1 : ℝ) ≤ 2)
  have hW : 0 ≤ Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hlocalCap : sigma * (Ch02.lambdaSq R (s / 6) (.finite 2) A)⁻¹ ≤
      Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ)) * K := by
    calc
      sigma * (Ch02.lambdaSq R (s / 6) (.finite 2) A)⁻¹ ≤
          sigma * (Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ)) *
            (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹) :=
        mul_le_mul_of_nonneg_left hloc hsigma.le
      _ = Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ)) *
          (sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹) := by ring
      _ ≤ Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ)) * K :=
        mul_le_mul_of_nonneg_left hlower hW
  exact lambdaS_inv_le_of_localRatioCap R A
    (by linarith only [hs] : 0 < s / 3) hsigma (by
      simpa [show s / 3 / 2 = s / 6 by ring] using hlocalCap)

/-- Arbitrary nonzero-boundary `H¹` data on a descendant inherit the
positive-side `circ` budget from the parent finite-`2` lower cap. -/
theorem aCutoff_h1Gradient_descendant_circPartialNorm_le_of_parent_sixth_cap
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q R : TriadicCube d} (u : H1Function (openCubeSet R))
    {s r sigma K : ℝ} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (hs : 0 < s)
    (hsr : s / 3 ≤ r) (hsigma : 0 < sigma)
    (hlower : sigma *
      (Ch02.lambdaSq Q (s / 6) (.finite 2) (aCutoffFamily M L omega))⁻¹ ≤ K)
    (i : Fin d) (N : ℕ) :
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * (j : ℝ))
    cubeBesovCircPartialNorm R r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x ↦ u.grad x i) ≤
      (cubeBesovScaleWeight (-r) R *
        ((geometricDiscount r 1)⁻¹ *
          ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))) *
        Real.sqrt (cubeAverage R
          (coefficientEnergyDensity
            (publicCoeffField R (aCutoffFamily M L omega)) u.grad)) := by
  dsimp only
  have hcap := descendant_lambdaS_inv_le_of_parent_sixth_cap
    (aCutoffFamily M L omega) hR hs hsigma hlower
  exact aCutoff_h1Gradient_circPartialNorm_le_of_lambdaSCap
    M L omega R u (div_pos hs (by norm_num)) hsr hcap i N

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
