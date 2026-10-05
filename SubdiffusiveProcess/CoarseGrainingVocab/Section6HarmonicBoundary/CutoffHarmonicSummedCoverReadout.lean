
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SummedCoverReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicLeaves

@[expose] public section

/-!
# The summed-cover energy readout, at a finite cutoff

Cutoff companion of
`Section6HarmonicApproximation.exists_invSqrt_mul_translatedCubeEnergy_le_of_boundaryCellHalfAbsorb`:
the binder `m ≤ L` is deleted and the good event is `𝒢^{(L)}_{n+2,z}`.  The
single changed leaf is the cutoff interior-cell manuscript price.

Argument: `l.harmonic.approximation.good.scales.GMC`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- Once the boundary descendants supply the adjustable-cutoff half row, the
full translated-cube energy has exactly the four first-order manuscript
prices.  In particular, neither cover geometry nor an interior-cell premise
survives this interface. -/
theorem exists_invSqrt_mul_translatedCubeEnergy_le_of_boundaryCellHalfAbsorb
    (d : ℕ) [NeZero d] :
    ∃ Cint : ℝ, 0 < Cint ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
      ∀ Cboundary : ℝ, 0 ≤ Cboundary →
        let D := translatedCube d ((n : ℤ) - 2) y
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        let parentBudget := sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
          normalizedL2On U
            (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2
        let affineBudget := if BoundaryTouches U (cube d (m : ℤ)) then
          sigma * vecNormSq (averageVecOn U h.grad) else 0
        let forceBudget := Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
          Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
          (fractionalSeminormOn U sOrder.1 g).toReal ^ 2
        let boundaryBudget := if BoundaryTouches U (cube d (m : ℤ)) then
          sigma * Real.rpow sOrder.1 (-4 : ℝ) *
            Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
            (fractionalSeminormOn U sOrder.1 h.grad).toReal ^ 2 else 0
        (∀ q,
          q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
          ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
          normalizedSetAverage
              (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
                _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
                  vecNormSq (u.grad p)) ≤
            Cboundary *
                (parentBudget + affineBudget + forceBudget + boundaryBudget) +
              (1 / 2 : ℝ) * normalizedSetAverage D (fun p ↦
                _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
                  vecNormSq (u.grad p))) →
        sigma ^ (-1 / 2 : ℝ) * vectorNormalizedL2On D (fun p ↦
            Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
              u.grad p) ≤
          Real.sqrt (2 * max Cint Cboundary) *
            ((3 : ℝ) ^ (-(n : ℤ)) *
                normalizedL2On U
                  (fun q ↦ u.toFun q - averageOn U u.toFun) +
              (if BoundaryTouches U (cube d (m : ℤ)) then
                Real.sqrt (vecNormSq (averageVecOn U h.grad)) else 0) +
              sigma⁻¹ * (Real.rpow sOrder.1 (-6 : ℝ) *
                Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal) +
              (if BoundaryTouches U (cube d (m : ℤ)) then
                Real.rpow sOrder.1 (-2 : ℝ) *
                  Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
                  (fractionalSeminormOn U sOrder.1 h.grad).toReal else 0)) := by
  obtain ⟨Cint, hCint, hinteriorCell⟩ :=
    exists_interiorCellEnergy_le_manuscriptPrices d
  refine ⟨Cint, hCint, ?_⟩
  intro M sOrder hs L m n hnm z x y omega hz hx hD hgood u h g
    hdir hg hh Cboundary hCboundary
  dsimp only
  intro hboundary
  let D := translatedCube d ((n : ℤ) - 2) y
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let O := normalizedL2On U
    (fun q ↦ u.toFun q - averageOn U u.toFun)
  let G := if BoundaryTouches U (cube d (m : ℤ)) then
    Real.sqrt (vecNormSq (averageVecOn U h.grad)) else 0
  let F := (fractionalSeminormOn U sOrder.1 g).toReal
  let H := if BoundaryTouches U (cube d (m : ℤ)) then
    (fractionalSeminormOn U sOrder.1 h.grad).toReal else 0
  let budgets := sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * O ^ 2 +
    sigma * G ^ 2 +
    Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
      Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) * F ^ 2 +
    sigma * Real.rpow sOrder.1 (-4 : ℝ) *
      Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) * H ^ 2
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hhFull : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad := by
    apply memCubeEuclideanFullWsp_grad_of_memFractionalOn
    simpa [cube] using hh
  have hO : 0 ≤ O := by dsimp [O, normalizedL2On]; exact Real.sqrt_nonneg _
  have hG : 0 ≤ G := by dsimp [G]; split <;> positivity
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hH : 0 ≤ H := by dsimp [H]; split <;> positivity
  have hbudgets : 0 ≤ budgets := by
    have hparent0 : 0 ≤ sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * O ^ 2 := by
      positivity
    have haffine0 : 0 ≤ sigma * G ^ 2 := mul_nonneg hsigma.le (sq_nonneg G)
    have hforce0 : 0 ≤ Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) * F ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg sOrder.2.1.le _)
            (inv_nonneg.mpr hsigma.le))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg F)
    have hboundary0 : 0 ≤ sigma * Real.rpow sOrder.1 (-4 : ℝ) *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) * H ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hsigma.le (Real.rpow_nonneg sOrder.2.1.le _))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg H)
    dsimp only [budgets]
    positivity
  have hinterior : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Cint * budgets := by
    intro q hq hpatch
    have hcell := hinteriorCell M sOrder hs L m n hnm z x q omega
      hz hx hq hpatch hgood u h g hdir hg hhFull
    dsimp only at hcell
    have hsmall :
        sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * O ^ 2 +
            Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
              Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) * F ^ 2 ≤
          budgets := by
      have haffine0 : 0 ≤ sigma * G ^ 2 := mul_nonneg hsigma.le (sq_nonneg G)
      have hboundary0 : 0 ≤ sigma * Real.rpow sOrder.1 (-4 : ℝ) *
          Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) * H ^ 2 := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg hsigma.le (Real.rpow_nonneg sOrder.2.1.le _))
            (Real.rpow_nonneg (by norm_num) _))
          (sq_nonneg H)
      dsimp only [budgets]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsmall hCint.le
    dsimp only [U, sigma, O, F] at hmul
    rw [show (n : ℤ) - 2 - 2 = (n : ℤ) - 4 by ring] at hcell
    exact hcell.trans hmul
  have hboundary' : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤
        Cboundary * budgets + (1 / 2 : ℝ) * normalizedSetAverage D (fun p ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
            vecNormSq (u.grad p)) := by
    intro q hq hpatch
    have hb := hboundary q hq hpatch
    by_cases ht : BoundaryTouches U (cube d (m : ℤ))
    · simpa [D, U, sigma, O, G, F, H, budgets, ht,
        Real.sq_sqrt (vecNormSq_nonneg _)] using hb
    · simpa [D, U, sigma, O, G, F, H, budgets, ht] using hb
  have henergy := normalizedCutoffEnergy_projectedCover_le_two_max_mul_of_half_absorb
    M L omega u hD hbudgets hinterior hboundary'
  have hK : 0 ≤ 2 * max Cint Cboundary := by
    exact mul_nonneg (by norm_num) (le_trans hCint.le (le_max_left _ _))
  have hout := invSqrt_mul_vectorNormalizedL2On_le_of_manuscriptFourBudgets
    D (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) u.grad
    (K := 2 * max Cint Cboundary) (sigma := sigma) (s := sOrder.1)
    (O := O) (G := G) (F := F) (H := H) (nr := (n : ℝ)) (n := (n : ℤ))
    (fun p ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega p).le)
    hK hsigma sOrder.2.1 hO hG hF hH henergy
  by_cases ht : BoundaryTouches U (cube d (m : ℤ))
  · simpa [D, U, sigma, O, G, F, H, ht] using hout
  · simpa [D, U, sigma, O, G, F, H, ht] using hout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
