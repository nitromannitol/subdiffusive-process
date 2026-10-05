module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPerCellClosure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszRepairedPointwiseDecay

@[expose] public section

/-!
# Graph-decay readout for the repaired stopping partition

The concrete scale-`m` repaired-cell local flux price that used to live here
(`exists_fluxRowRiesz_repairedStoppingCell_localFluxPrice`) is **retired**: its
conclusion priced `fluxRowRieszLocalNegative (refinedStoppingScale q)`, the
scale-normalized negative dual on the scale-`m` cube, which is neither the cube
the cutoff pairing is supported on nor the coefficient that pairing produces
The live replacement is
`exists_fluxRowSlots_repairedStoppingCell_enlargedLocalFluxPrice`
(`FluxRowSlotsEnlargedPrice.lean`), on the enlargement `Q̂` and in the physical
dual coefficient `Nq`.

What remains here is the graph-decay readout used by the enlargement mass
estimate.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.Frozen.Section8
open scoped ENNReal

noncomputable section

/-- The paper's half-distance real power of a square is the integer power of the
base.  This is the identity that matches the pointwise repaired-graph decay to
the `theta ^ (dist / 2)` slot of `fluxRowRieszCellPhysicalScale`. -/
theorem fluxRowRiesz_rpow_half_sq {theta : ℝ} (htheta : 0 ≤ theta) (j : ℕ) :
    Real.rpow (theta ^ 2) ((j : ℝ) / 2) = theta ^ j := by
  have hsq : Real.rpow theta 2 = theta ^ 2 := by
    simp
  have hhalf : Real.rpow (theta ^ 2) (1 / 2 : ℝ) = theta := by
    rw [← hsq]
    calc Real.rpow (Real.rpow theta 2) (1 / 2 : ℝ)
        = Real.rpow theta (2 * (1 / 2 : ℝ)) :=
          (Real.rpow_mul htheta 2 (1 / 2 : ℝ)).symm
      _ = Real.rpow theta 1 := by norm_num
      _ = theta := Real.rpow_one theta
  calc Real.rpow (theta ^ 2) ((j : ℝ) / 2)
      = Real.rpow (theta ^ 2) ((1 / 2 : ℝ) * (j : ℝ)) := by ring_nf
    _ = Real.rpow (Real.rpow (theta ^ 2) (1 / 2 : ℝ)) (j : ℝ) :=
        Real.rpow_mul (sq_nonneg theta) (1 / 2 : ℝ) (j : ℝ)
    _ = Real.rpow theta (j : ℝ) := by rw [hhalf]
    _ = theta ^ j := Real.rpow_natCast _ _

/-- **The pointwise repaired-graph decay in the price's `theta` slot.**  With
`theta` the square of the pointwise contraction factor, the proved decay is
literally the factor `theta ^ (dist(Q, C) / 2)` appearing in
`fluxRowRieszCellPhysicalScale`. -/
theorem wholeSpaceSolution_cell_mass_le_rpow_half_repairedStoppingDecay
    {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂MeasureTheory.volume ≤
      ∫ x, f x ^ 2 ∂MeasureTheory.volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
        ∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂MeasureTheory.volume ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂MeasureTheory.volume) :
    ∀ q,
      ∫ x in translatedCube d (refinedStoppingScale q)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂MeasureTheory.volume ≤
        Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
            ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ) / 2) *
          ∫ x, f x ^ 2 ∂MeasureTheory.volume := by
  intro q
  rw [fluxRowRiesz_rpow_half_sq
    repairedStoppingPointwiseContractionFactor_pos.le
    (stoppingGraphDistance repairedStoppingGraph source hsource q)]
  exact wholeSpaceSolution_cell_mass_le_repairedStoppingPointwiseDecay u hL2
    hinitial hrepair source hsource hcell q

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
