module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoGateScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoCoverApplied
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoProjectedEnergy

@[expose] public section

/-!
# Boundary Holder row two: projected energy at the selected gate

The outer-boundary projected-energy producer is applied at the good gate and
then transported from `gate - 4` to the requested base scale.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The four-budget outer projected energy at a selected good gate, read at
the base scale. -/
theorem exists_boundaryRowTwoGateBudget (d : ℕ) [NeZero d] :
    ∃ Kb : ℝ, 0 < Kb ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        (interiorFractionalOrder).1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ L m n gate : ℕ, m ≤ L → n + 4 ≤ gate → gate + 5 ≤ m →
      ∀ x z : Vec d, ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        x ∈ cube d (m : ℤ) → z ∈ cube d (m : ℤ) →
        (∀ i : Fin d, |x i - z i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n) →
        omega ∈ goodEvent M none (gate + 2) z 1
          ((interiorFractionalOrder).1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        MemHolder (cube d (m : ℤ)) (1 / 2) h.grad →
        vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
            (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
              u.grad p) ≤
          scaleTransferPrice d ((gate : ℤ) - 4 - (n : ℤ)) *
            Real.sqrt ((81 : ℝ) ^ d *
              (Kb * harmonicPhysicalFourBudgets M L m gate z x omega
                (interiorFractionalOrder).1 u h g)) := by
  obtain ⟨Kb, hKb, hstep6⟩ := exists_boundaryHolderProjectedEnergy d
  refine ⟨Kb, hKb, ?_⟩
  intro M hs L m n gate hmL hngate hgatem x z omega hxm hz hdist hgood
    u h g hsol hg hh
  have hxmem : x ∈ truncatedCube d (m : ℤ) ((gate : ℤ) - 3) z := by
    refine mem_truncatedCube_of_dist hxm ?_
    intro i
    refine lt_of_le_of_lt (hdist i) ?_
    have hlt : (3 : ℝ) ^ (n : ℤ) < (3 : ℝ) ^ ((gate : ℤ) - 3) := by
      refine zpow_lt_zpow_right₀ (by norm_num) ?_
      omega
    have hpow : (3 : ℝ) ^ (n : ℕ) = (3 : ℝ) ^ (n : ℤ) := by
      rw [zpow_natCast]
    rw [hpow]
    linarith
  have hgWsp : Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d (m : ℤ))
      interiorFractionalOrder FiniteLpExponent.two g :=
    Section6ExcessDecay.memCubeEuclideanFullWsp_cube_of_memHolder
      (Nat.one_le_iff_ne_zero.2 (NeZero.ne d)) interiorFractionalOrder
      (by rw [interiorFractionalOrder_val]) hg
  have hhFrac : MemFractionalOn (cube d (m : ℤ))
      (interiorFractionalOrder).1 h.grad :=
    Section6ExcessDecay.memFractionalOn_cube_of_memHolder
      (Nat.one_le_iff_ne_zero.2 (NeZero.ne d)) interiorFractionalOrder.2.1
      (by rw [interiorFractionalOrder_val]) hh
  have hgate := hstep6 M interiorFractionalOrder hs L m gate hmL (by omega)
    z x omega hz hxmem hgood u h g hsol hgWsp hhFrac
  have htrans := weightedGrad_scaleTransfer M L omega u (m := (m : ℤ))
    (n := (n : ℤ)) (j := (gate : ℤ) - 4) (y := x) hxm (by omega) (by omega)
    (by omega)
  unfold weightedGrad at htrans
  refine htrans.trans ?_
  exact mul_le_mul_of_nonneg_left hgate (scaleTransferPrice_nonneg d _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
