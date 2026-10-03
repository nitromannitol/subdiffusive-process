module

public import SubdiffusiveProcess.BoundedMultiplier.OuterOscillation
public import SubdiffusiveProcess.Frozen.Section6.CutoffHolderBoundedMultiplier

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper



theorem p_cutoff_Holder_bounded_multiplier (d : ℕ) :
    ∃ epsilonStar c C : ℝ, 0 < epsilonStar ∧ 0 < c ∧ 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d, ∀ j : ℕ, 0 < j →
        let B := translatedCube d m z
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ bad : Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
            @MeasurableSet (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
                (restrictedCoefficientSigma (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L) B) bad ∧
            M.P.toMeasure bad ≤ ENNReal.ofReal
              (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ ω ∉ bad, ∀ theta : Vec d → ℝ,
              ContinuousOn theta B → (∀ x ∈ B, 0 < theta x) →
              (∀ ε' : ℝ, epsilonStar < ε' → ∃ b : ℝ, 0 < b ∧ ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ ε') →
              ∀ h : H1Function B, IsWeaklyHarmonicOn
                  (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x * theta x) B h →
                ∃ hRep : Vec d → ℝ,
                  ContinuousOn hRep B ∧
                  hRep =ᵐ[volume.restrict B] h.toFun ∧
                  ENNReal.ofReal (oscillationOn B' hRep) ≤
                    ENNReal.ofReal (C * (3 : ℝ) ^ (-c * j)) *
                      ⨆ x ∈ B, ⨆ y ∈ B, ENNReal.ofReal |hRep x - hRep y| ∧
                  sSup {r : ℝ | ∃ x ∈ B', r = |hRep x - averageOn B hRep|} ≤
                    C * normalizedL2On B (fun x => hRep x - averageOn B hRep) := by
  obtain ⟨epsilon, c, C, hepsilon, hc, hC, hmain⟩ :=
    SubdiffusiveProcess.BoundedMultiplier.exists_restricted_estimate d
  refine ⟨epsilon / 2, c, C, half_pos hepsilon, hc, hC, ?_⟩
  intro M hdelta L m z j hj
  dsimp only
  intro B' hB'
  obtain ⟨bad, hmeas, htail, hpath⟩ := hmain M hdelta L m z j hj B' hB'
  refine ⟨bad, hmeas, htail, ?_⟩
  intro w hw theta hcont hpos hnear h hharm
  obtain ⟨b, hb, hclose⟩ := hnear epsilon (by linarith)
  obtain ⟨hRep, hRepCont, hRepAE, hosc, hL2⟩ :=
    hpath w hw theta hcont hpos ⟨b, hb, hclose⟩ h hharm
  refine ⟨hRep, hRepCont, hRepAE, ?_, hL2⟩
  exact SubdiffusiveProcess.BoundedMultiplier.ofReal_oscillation_estimate
    m z B' hRep (mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) _)) hosc

end Paper
