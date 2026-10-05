module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedExteriorL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedFluxDecay

@[expose] public section

/-!
# Pointwise decay on the repaired stopping graph

The local flux price contains the factor `theta^(dist(Q,C)/2)`.  This file
builds its cell-mass input on the actual repaired carrier.  The centered
enlargement of a cell is covered by its repaired closed neighbors, so the
local contraction loses exactly their cardinality.  The resulting pointwise
factor is `(D(d) + 1) * repairedStoppingContractionFactor d`.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.Frozen.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- The neighbor-cover loss in the pointwise repaired-graph decay. -/
def repairedStoppingPointwiseContractionFactor (d : ℕ) : ℝ :=
  ((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) *
    repairedStoppingContractionFactor d

omit [NeZero d] in
theorem repairedStoppingPointwiseContractionFactor_pos :
    0 < repairedStoppingPointwiseContractionFactor d := by
  unfold repairedStoppingPointwiseContractionFactor
  exact mul_pos (by positivity) repairedStoppingContractionFactor_pos

omit [NeZero d] in
theorem repairedStoppingPointwiseContractionFactor_lt_one :
    repairedStoppingPointwiseContractionFactor d < 1 := by
  have hD : 1 ≤ (repairedStoppingDegreeBound d : ℝ) := by
    exact_mod_cast repairedStoppingDegreeBound_pos (d := d)
  have htheta : 0 ≤ repairedStoppingPointwiseContractionFactor d :=
    repairedStoppingPointwiseContractionFactor_pos.le
  have hmul : (repairedStoppingDegreeBound d : ℝ) *
      repairedStoppingPointwiseContractionFactor d = 1 / 2 := by
    simpa only [repairedStoppingPointwiseContractionFactor] using
      (repairedStopping_effectiveContraction_eq_half (d := d))
  calc
    repairedStoppingPointwiseContractionFactor d ≤
        (repairedStoppingDegreeBound d : ℝ) *
          repairedStoppingPointwiseContractionFactor d := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD htheta
    _ = 1 / 2 := hmul
    _ < 1 := by norm_num

/-- Local repaired-cell contractions imply pointwise graph-distance decay.

The global `L²` contraction controls every source cell and bounds the tail
supremum.  The repaired closed-neighbor cover supplies the one-step graph
recursion, including its exact `D(d) + 1` multiplicity. -/
theorem wholeSpaceSolution_cell_mass_le_repairedStoppingPointwiseDecay
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
        ∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume) :
    ∀ q,
      ∫ x in translatedCube d (refinedStoppingScale q)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
        repairedStoppingPointwiseContractionFactor d ^
            stoppingGraphDistance repairedStoppingGraph source hsource q *
          ∫ x, f x ^ 2 ∂volume := by
  let mass : RefinedStoppingCell failure omega base → ℝ := fun q ↦
    ∫ x in translatedCube d (refinedStoppingScale q)
      (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume
  let level : RefinedStoppingCell failure omega base → ℕ :=
    stoppingGraphDistance repairedStoppingGraph source hsource
  have hfEnergy : 0 ≤ ∫ x, f x ^ 2 ∂volume :=
    integral_nonneg fun x ↦ sq_nonneg (f x)
  have hmassBound : ∀ q, mass q ≤ ∫ x, f x ^ 2 ∂volume := by
    intro q
    exact (setIntegral_sq_refinedStoppingCell_le_integral_sq u q).trans hL2
  have hsourceMass : ∀ q, level q = 0 →
      mass q ≤ ∫ x, f x ^ 2 ∂volume := by
    intro q _
    exact hmassBound q
  have hstep : ∀ q, 0 < level q →
      ∃ p, level q ≤ level p + 1 ∧
        mass q ≤ repairedStoppingPointwiseContractionFactor d * mass p := by
    intro q hq
    obtain ⟨p, hp, hmassCover⟩ :=
      exists_mem_integral_sq_le_card_mul_of_finset_cover u.memL2_toFun
        (repairedStoppingClosedNeighbors q)
        (repairedStoppingClosedNeighbors_nonempty q)
        (fun p ↦ translatedCube d (refinedStoppingScale p)
          (refinedStoppingCenter p))
        (refinedStoppingCell_enlargement_subset_iUnion_closedNeighbors
          hinitial hrepair q)
    refine ⟨p, ?_, ?_⟩
    · rcases eq_or_adj_of_mem_repairedStoppingClosedNeighbors hp with rfl | hadj
      · omega
      · exact repairedStoppingGraphDistance_le_succ_of_adj hinitial hrepair
          source hsource hadj
    · have htheta : 0 ≤ repairedStoppingContractionFactor d :=
        repairedStoppingContractionFactor_pos.le
      have hmassp : 0 ≤ mass p := by
        exact setIntegral_nonneg
          (isOpenBoundedConvexDomain_translatedCube (d := d)
            (refinedStoppingScale p)
            (refinedStoppingCenter p)).isOpen.measurableSet
          fun x _ ↦ sq_nonneg (u.toFun x)
      have hcard : ((repairedStoppingClosedNeighbors q).card : ℝ) ≤
          ((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) := by
        exact_mod_cast card_repairedStoppingClosedNeighbors_le q
      calc
        mass q ≤ repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume := hcell q hq
        _ ≤ repairedStoppingContractionFactor d *
            (((repairedStoppingClosedNeighbors q).card : ℝ) * mass p) :=
          mul_le_mul_of_nonneg_left hmassCover htheta
        _ ≤ repairedStoppingContractionFactor d *
            (((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) * mass p) := by
          gcongr
        _ = repairedStoppingPointwiseContractionFactor d * mass p := by
          unfold repairedStoppingPointwiseContractionFactor
          ring
  exact cell_mass_le_geometric_of_step mass level hfEnergy hfEnergy
    repairedStoppingPointwiseContractionFactor_pos.le
    repairedStoppingPointwiseContractionFactor_lt_one hmassBound hsourceMass hstep

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
