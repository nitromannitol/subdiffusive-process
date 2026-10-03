module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedOrders
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedPrebalance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourcePrebalanceComposition

@[expose] public section

/-!
# Balancing the source-scale Dirichlet prebalance row
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The deterministic coefficient multiplying the optimizing-scale core after
the source and physical energy prices have been inserted. -/
def cutoffDirichletSourceCoefficient
    (d : ℕ) [NeZero d] (Ccg Cenergy vartheta : ℝ)
    (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1) : ℝ :=
  sourceDirichletPrebalanceConstant Ccg
    (dirichletS vartheta) (dirichletS2 vartheta)
    (dirichletWeightedEnergyFactor
      (dirichletS1 vartheta) (dirichletS vartheta))
    (sourceDirichletEnergyConstant d Cenergy
      (dirichletS1Order vartheta hvartheta))
    (sourceDirichletFractionalDatumConstant d
      (dirichletS2Order vartheta hvartheta))

theorem cutoffDirichletSourceCoefficient_nonneg
    (d : ℕ) [NeZero d] {Ccg Cenergy vartheta : ℝ}
    (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1)
    (hCcg : 0 ≤ Ccg) (hCenergy : 0 ≤ Cenergy) :
    0 ≤ cutoffDirichletSourceCoefficient d Ccg Cenergy vartheta hvartheta := by
  apply sourceDirichletPrebalanceConstant_nonneg hCcg
  · exact (dirichletSOrder vartheta hvartheta).2.1
  · exact dirichletSOrder_lt_dirichletS2Order vartheta hvartheta
  · exact dirichletWeightedEnergyFactor_nonneg _ _
  · exact sourceDirichletEnergyConstant_nonneg d hCenergy _
  · exact sourceDirichletFractionalDatumConstant_nonneg d _

/-- Lift the real optimizing-scale balance through `ENNReal.ofReal`. -/
theorem ENNReal.le_balancedDirichletRandomFactor_of_prebalance
    {X : ℝ≥0∞}
    {C delta vartheta s1 s2 E1 E2 Y D : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hE1 : 0 ≤ E1) (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (hpre : X ≤ ENNReal.ofReal
      (C * dirichletPrebalanceCore s1 s2 k E1 E2 Y * D)) :
    X ≤ ENNReal.ofReal
      (dirichletRandomFactor C delta vartheta s1 s2 k
          (fun _ : Unit ↦ E1) (fun _ : Unit ↦ E2)
          (fun _ : Unit ↦ Y) () * Real.rpow delta vartheta * D) := by
  exact hpre.trans (ENNReal.ofReal_le_ofReal
    (mul_dirichletPrebalanceCore_mul_le_randomFactor_mul_rpow_mul
      hC hdelta hE1 hY hD))

/-- Specialized spelling with the concrete coefficient-measurable universal
random factor. -/
theorem ENNReal.le_dirichletUniversalRandomFactor_of_prebalance
    {d : ℕ} {X : ℝ≥0∞}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {C vartheta D : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hpre : X ≤ ENNReal.ofReal
      (C * dirichletPrebalanceCore
        (dirichletS1 vartheta) (dirichletS2 vartheta) k
        (dirichletFullResponseOne M L N (dirichletS1 vartheta) omega)
        (dirichletFullResponseTwo M L N (dirichletS1 vartheta) omega)
        (dirichletEllipticityEnvelope M L N (dirichletS1 vartheta) omega) * D)) :
    X ≤ ENNReal.ofReal
      (dirichletUniversalRandomFactor M L N C M.delta vartheta
          (dirichletS1 vartheta) (dirichletS2 vartheta) k omega *
        Real.rpow M.delta vartheta * D) := by
  exact ENNReal.le_balancedDirichletRandomFactor_of_prebalance
    hC M.shellPrefix.delta_pos
    (dirichletFullResponseOne_nonneg M L N (dirichletS1 vartheta) omega)
    (zero_le_one.trans
      (one_le_dirichletEllipticityEnvelope M L N (dirichletS1 vartheta) omega))
    hD hpre

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
