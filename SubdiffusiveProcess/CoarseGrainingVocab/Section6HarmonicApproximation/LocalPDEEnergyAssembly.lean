module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellCollapsed
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ProjectedCoverAssembly

@[expose] public section

/-!
# Mixed-cover assembly for the harmonic-approximation energy display

This file isolates the final deterministic finite-cover step in the proof of
`l.harmonic.approximation.good.scales.GMC`.  The interior cell estimate is
already proved.  The only exposed input is the corresponding boundary-cell
estimate with the four manuscript square budgets.

The fixed projected `9^d` cover uses the scalar GMC energy and the parent, affine, forcing, and boundary-datum bounds.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- The mixed projected cover has no remaining geometric premise once the
boundary cells satisfy the printed four-budget estimate.  This theorem is the
exact assembly seam between the missing nonzero-boundary Caccioppoli input and
the translated-cube energy display. -/
theorem exists_translatedCube_energy_le_of_boundaryCellManuscriptBound
    (d : ℕ) [NeZero d] :
    ∃ Cint : ℝ, 0 < Cint ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
      ∀ Cboundary : ℝ, 0 ≤ Cboundary →
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
              (parentBudget + affineBudget + forceBudget + boundaryBudget)) →
        normalizedSetAverage (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
          max Cint Cboundary *
            (parentBudget + affineBudget + forceBudget + boundaryBudget) := by
  obtain ⟨Cint, hCint, hinteriorCell⟩ :=
    exists_interiorCellEnergy_le_manuscriptPrices d
  refine ⟨Cint, hCint, ?_⟩
  intro M sOrder hs L m n hmL hnm z x y omega hz hx hD hgood u h g
    hdir hg hh Cboundary hCboundary
  dsimp only
  intro hboundary
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let parentBudget := sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
    normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun) ^ 2
  let affineBudget := if BoundaryTouches U (cube d (m : ℤ)) then
    sigma * vecNormSq (averageVecOn U h.grad) else 0
  let forceBudget := Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
    Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
    (fractionalSeminormOn U sOrder.1 g).toReal ^ 2
  let boundaryBudget := if BoundaryTouches U (cube d (m : ℤ)) then
    sigma * Real.rpow sOrder.1 (-4 : ℝ) *
      Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
      (fractionalSeminormOn U sOrder.1 h.grad).toReal ^ 2 else 0
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
  have hparent0 : 0 ≤ parentBudget := by
    dsimp [parentBudget]
    positivity
  have haffine0 : 0 ≤ affineBudget := by
    dsimp [affineBudget]
    split
    · exact mul_nonneg hsigma.le (vecNormSq_nonneg _)
    · exact le_rfl
  have hforce0 : 0 ≤ forceBudget := by
    dsimp [forceBudget]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg sOrder.2.1.le _)
          (inv_nonneg.mpr hsigma.le))
        (Real.rpow_nonneg (by norm_num) _))
      (sq_nonneg _)
  have hboundary0 : 0 ≤ boundaryBudget := by
    dsimp [boundaryBudget]
    split
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hsigma.le (Real.rpow_nonneg sOrder.2.1.le _))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    · exact le_rfl
  let Bint := Cint * (parentBudget + forceBudget)
  let Bboundary := Cboundary *
    (parentBudget + affineBudget + forceBudget + boundaryBudget)
  have hcover := normalizedCutoffEnergy_projectedCover_le_max
    M L omega u hD Bint Bboundary
  have hinterior : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Bint := by
    intro q hq hpatch
    have hcell := hinteriorCell M sOrder hs L m n hmL hnm z x q omega
      hz hx hq hpatch hgood u h g hdir hg hhFull
    dsimp only at hcell
    change _ ≤ Bint
    dsimp only [Bint, parentBudget, forceBudget, U, sigma]
    rw [show (n : ℤ) - 2 - 2 = (n : ℤ) - 4 by ring] at hcell
    exact hcell
  have hraw : normalizedSetAverage (translatedCube d ((n : ℤ) - 2) y)
        (fun p ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
          vecNormSq (u.grad p)) ≤ max Bint Bboundary :=
    hcover hinterior (by
      intro q hq hpatch
      simpa only [Bboundary, parentBudget, affineBudget, forceBudget,
        boundaryBudget, U, sigma] using hboundary q hq hpatch)
  have hBint : Bint ≤ max Cint Cboundary *
      (parentBudget + affineBudget + forceBudget + boundaryBudget) := by
    have hcoef := le_max_left Cint Cboundary
    have hsmall : parentBudget + forceBudget ≤
        parentBudget + affineBudget + forceBudget + boundaryBudget := by
      linarith
    calc
      Bint = Cint * (parentBudget + forceBudget) := rfl
      _ ≤ max Cint Cboundary * (parentBudget + forceBudget) :=
        mul_le_mul_of_nonneg_right hcoef (add_nonneg hparent0 hforce0)
      _ ≤ max Cint Cboundary *
          (parentBudget + affineBudget + forceBudget + boundaryBudget) :=
        mul_le_mul_of_nonneg_left hsmall
          (le_trans hCint.le (le_max_left Cint Cboundary))
  have hBboundary : Bboundary ≤ max Cint Cboundary *
      (parentBudget + affineBudget + forceBudget + boundaryBudget) := by
    exact mul_le_mul_of_nonneg_right (le_max_right Cint Cboundary)
      (by positivity)
  exact hraw.trans <| max_le hBint hBboundary

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
