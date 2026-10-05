module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellCollapsed
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.EnergyCover
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyCover
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffCellEnergy

@[expose] public section

/-!
# Interior Hölder Step 6, unconditional

The harmonic-approximation argument's datum-free companion
`Section6HarmonicApproximation.exists_interiorCellEnergy_le_manuscriptPrices_weak`
is byte-for-byte the shape recorded as `InteriorCellEnergyInput_cut`, so the
interior cell price discharges by one application.  Combined with
`exists_interiorHolderProjectedEnergy_cut` — whose boundary-cell budget is vacuous
at an interior base point — **Step 6 of the interior ladder is unconditional**.

This is the point at which the interior anchor overtakes the boundary one: the
boundary argument's Step 6 still owes the affine-covariant active-cell remainder for
its boundary cells, a branch the interior re-cut does not have.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch01 Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {L : ℕ}
attribute [local instance] Classical.propDecidable

/-- The interior cell price, datum-free, from the harmonic-approximation argument. -/
theorem interiorCellEnergyInput_of_harmonicApproximation_cut (d : ℕ) [NeZero d] :
    InteriorCellEnergyInput_cut d :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.exists_interiorCellEnergy_le_manuscriptPrices_cutoff d

/-- **Interior Step 6, with no premise left.**  The projected energy cover at an
interior base point, priced by the parent oscillation and the source term
alone. -/
theorem exists_interiorHolderProjectedEnergy_final_cut (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d ((m : ℤ) - 1) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        vectorNormalizedL2On
            (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
            (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
              u.grad p) ≤
          Real.sqrt ((81 : ℝ) ^ d *
            (K * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                  normalizedL2On U
                    (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 +
                Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                  Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                  (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))) :=
  exists_interiorHolderProjectedEnergy_cut d (interiorCellEnergyInput_of_harmonicApproximation_cut d)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
