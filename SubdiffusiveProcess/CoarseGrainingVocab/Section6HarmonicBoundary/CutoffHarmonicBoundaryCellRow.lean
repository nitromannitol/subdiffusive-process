/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicSummedCoverReadout




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]



def BoundaryCellManuscriptRow (d : ℕ) (Cboundary : ℝ) : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sOrder : FractionalOrder),
    sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
  ∀ (L m n : ℕ), n + 5 ≤ m →
  ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
    z ∈ cube d (m : ℤ) →
    x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
    q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
    ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
    omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
  ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d),
    IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (originCube d (m : ℤ)) u h g →
    Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
    MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
    normalizedSetAverage (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)
        (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (u.grad p)) ≤
      Cboundary *
        harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g

/-- **The weighted-energy slot from the boundary-cell row.**

Companion of
`Section6HarmonicApproximation.exists_boundaryWeightedEnergySlot_of_physicalRecurrence`
with the radius recurrence replaced by the manuscript's own local control row.
The conclusion is byte-identical to that theorem's. -/
theorem exists_boundaryWeightedEnergySlot_of_cellRow
    (d : ℕ) [NeZero d] {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hrow : BoundaryCellManuscriptRow d Cb) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
      ∀ (u0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2)))),
        (∀ p, u0.grad p = u.grad (p + y)) →
      ∀ (s1 smid : FractionalOrder), s1.1 < smid.1 →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        let B := (3 : ℝ) ^ (-(n : ℤ)) *
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
                (fractionalSeminormOn U sOrder.1 h.grad).toReal else 0)
        Ch03.ABK26.weightedLocalSymmetricEnergyLp
            (originCube d ((n : ℤ) - 2))
            ((originCube d ((n : ℤ) - 2)).scale - 1) (by omega)
            ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
              (originCube d ((n : ℤ) - 2))) u0 s1 smid
              FiniteLpExponent.two ≤
          ENNReal.ofReal
            (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
              (Real.sqrt sigma * (C * B))) := by
  obtain ⟨Cint, hCint, hread⟩ :=
    exists_invSqrt_mul_translatedCubeEnergy_le_of_boundaryCellHalfAbsorb d
  have hmax : 0 < 2 * max Cint Cb := by
    have : Cint ≤ max Cint Cb := le_max_left _ _
    linarith
  refine ⟨Real.sqrt (2 * max Cint Cb), Real.sqrt_pos.mpr hmax, ?_⟩
  intro M sOrder hs L m n hnm z x y omega hz hx hD hgood u h g hdir hg hh
    u0 hu0grad s1 smid hgap
  dsimp only
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have henergyNonneg : ∀ p,
      0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p) :=
    fun p ↦ mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega p).le
      (vecNormSq_nonneg _)
  have hEnonneg : 0 ≤ normalizedSetAverage
      (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) :=
    volumeAverage_nonneg_of_nonneg_on
      (Section6Schauder.measurableSet_translatedCube d ((n : ℤ) - 2) y)
      (fun p _ ↦ henergyNonneg p)
  have hcells : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤
        Cb * harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g +
          (1 / 2 : ℝ) * normalizedSetAverage
            (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
                vecNormSq (u.grad p)) := by
    intro q hq hbd
    have := hrow M sOrder hs L m n hnm z x q omega hz hx hq hbd hgood
      u h g hdir hg hh
    linarith [hEnonneg]
  have hout := hread M sOrder hs L m n hnm z x y omega hz hx hD hgood
    u h g hdir hg hh Cb hCb (by
      simpa only [harmonicPhysicalFourBudgets] using hcells)
  exact weightedLocalSymmetricEnergyLp_two_le_of_physicalEnergyReadout
    M L omega ((n : ℤ) - 2) y u0 u.grad hu0grad s1 smid hgap
    (sigma := tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z))
    hsigma hout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
