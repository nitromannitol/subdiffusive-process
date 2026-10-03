module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.EnergyRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoCoverApplied
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowTwoGateScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoGateScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.GateParameters

@[expose] public section

/-!
# Interior Step 6 at the gate scale, transported down to the frozen base scale

Interior Step 6 (`EnergyRow.exists_interiorHolderProjectedEnergy_final_cut`,
unconditional) controls the weighted gradient on `U_{m,gate-4}(x)`.  Frozen
row 2 asks for the same quantity on `U_{m,n}(x)` with `n` the base scale, and
`n ≤ gate - 4`, so the passage is one window inclusion at a fixed centre —
`EnergyScaleTransfer.vectorNormalizedL2On_scaleTransfer`, whose price
`scaleTransferPrice d (gate - 4 - n)` is `3^{d(gate-n-2)/2}` and therefore of
the `exp(C lambda (m-n))` type the row-1 absorption already converts into a
fraction of the frozen gap gain.

The good-event centre is a scale-`n` grid point of `cu_{m-1}` within `3^n / 2`
of the frozen base point, so Step 6's interiority binder `z ∈ cu_{m-1}` is met
verbatim — no gated re-cut is needed — and the containment binder
`x ∈ U_{m,gate-3}(z)` follows from `n + 4 ≤ gate`.

The datum hypothesis of Step 6 is the Chapter 3 finite-`p` fractional carrier;
`Section6ExcessDecay.memCubeEuclideanFullWsp_cube_of_memHolder` produces it from
the frozen Hölder datum at the gate's own order `1/4`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization Homogenization.Book Homogenization.Book.Ch03

noncomputable section

variable {L : ℕ}
attribute [local instance] Classical.propDecidable

/-- **Interior Step 6 at the gate scale, read at the frozen base scale.** -/
theorem exists_interiorRowTwoGateBudget_cut (d : ℕ) [NeZero d] :
    ∃ Kb : ℝ, 0 < Kb ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        (interiorFractionalOrder_cut).1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ L m n gate : ℕ, n + 4 ≤ gate → gate + 5 ≤ m →
      ∀ x z : Vec d, ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        x ∈ cube d (m : ℤ) → z ∈ cube d ((m : ℤ) - 1) →
        (∀ i : Fin d, |x i - z i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n) →
        omega ∈ goodEvent M (some L) (gate + 2) z 1
          ((interiorFractionalOrder_cut).1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) ≤
          scaleTransferPrice d ((gate : ℤ) - 4 - (n : ℤ)) *
            Real.sqrt ((81 : ℝ) ^ d *
              (Kb * (tailAverage M L (gate + 2) omega
                    (translatedCube d ((gate : ℤ) + 2) z) *
                  (3 : ℝ) ^ (-(2 * (gate : ℤ))) *
                  normalizedL2On (truncatedCube d (m : ℤ) (gate : ℤ) x)
                    (fun p ↦ u.toFun p -
                      averageOn (truncatedCube d (m : ℤ) (gate : ℤ) x)
                        u.toFun) ^ 2 +
                (interiorFractionalOrder_cut).1 ^ (-12 : ℝ) *
                  (tailAverage M L (gate + 2) omega
                    (translatedCube d ((gate : ℤ) + 2) z))⁻¹ *
                  (3 : ℝ) ^ (2 * (interiorFractionalOrder_cut).1 * (gate : ℝ)) *
                  (fractionalSeminormOn (truncatedCube d (m : ℤ) (gate : ℤ) x)
                    (interiorFractionalOrder_cut).1 g).toReal ^ 2))) := by
  obtain ⟨Kb, hKb, hstep6⟩ := exists_interiorHolderProjectedEnergy_final_cut d
  refine ⟨Kb, hKb, ?_⟩
  intro M hs L m n gate hngate hgatem x z omega hxm hz hdist hgood u g hsol hg
  -- the containment side condition
  have hxmem : x ∈ truncatedCube d (m : ℤ) ((gate : ℤ) - 3) z := by
    refine mem_truncatedCube_of_dist_cut hxm ?_
    intro i
    refine lt_of_le_of_lt (hdist i) ?_
    have hlt : (3 : ℝ) ^ (n : ℤ) < (3 : ℝ) ^ ((gate : ℤ) - 3) := by
      refine zpow_lt_zpow_right₀ (by norm_num) ?_
      omega
    have hpow : (3 : ℝ) ^ (n : ℕ) = (3 : ℝ) ^ (n : ℤ) := by
      rw [zpow_natCast]
    rw [hpow]
    linarith
  -- the Chapter 3 datum carrier from the frozen Hölder datum
  have hgWsp : Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d (m : ℤ))
      interiorFractionalOrder_cut FiniteLpExponent.two g :=
    Section6ExcessDecay.memCubeEuclideanFullWsp_cube_of_memHolder
      (Nat.one_le_iff_ne_zero.2 (NeZero.ne d)) interiorFractionalOrder_cut
      (by rw [interiorFractionalOrder_val]) hg
  have hgate := hstep6 M interiorFractionalOrder_cut hs L m gate (by omega)
    z x omega hz hxmem hgood u g hsol hgWsp
  dsimp only at hgate
  -- the scale transfer at a fixed centre
  have htrans := weightedGrad_scaleTransfer M L omega u (m := (m : ℤ))
    (n := (n : ℤ)) (j := (gate : ℤ) - 4) (y := x) hxm (by omega) (by omega)
    (by omega)
  unfold weightedGrad at htrans
  refine htrans.trans ?_
  exact mul_le_mul_of_nonneg_left hgate (scaleTransferPrice_nonneg d _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
