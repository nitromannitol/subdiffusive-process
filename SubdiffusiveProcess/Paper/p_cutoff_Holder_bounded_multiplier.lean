module

public import SubdiffusiveProcess.BoundedMultiplier.OuterOscillation
public import SubdiffusiveProcess.Section6.CutoffHolderBoundedMultiplier

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Paper

/-- **Proposition `p.cutoff.Holder.bounded.multiplier`** (paper label `p.cutoff.Holder.bounded.multiplier`, ).

Proved.  The only difference from the existing theorem
`SubdiffusiveProcess.Section6.cutoff_holder_bounded_multiplier` is the localization of the exceptional
event: the paper asserts that `bad` is measurable with respect to `a_L|_B`
(`restrictedCoefficientSigma (aCutoff M L) B`), whereas the proof step asserts
measurability for the ambient product σ-field.  The remaining differences are stated exactly as in the paper:
the multiplier hypothesis is `inf_{b>0} ‖b⁻¹θ − 1‖_{L^∞(B)} ≤ ε_*` (written without junk values as
`∀ ε' > ε_*, ∃ b > 0, ∀ x ∈ B, |b⁻¹θ(x) − 1| ≤ ε'`) and the oscillation on the right is over all of `B`
(`ℝ≥0∞`-valued, so that an unbounded `h` gives a trivial bound rather than the junk value `sSup = 0`). -/
theorem p_cutoff_Holder_bounded_multiplier (d : ℕ) :
    ∃ epsilonStar c C : ℝ, 0 < epsilonStar ∧ 0 < c ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d, ∀ j : ℕ, 0 < j →
        let B := translatedCube d m z
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ bad : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d),
            @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialSample d)
                (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B) bad ∧
            M.P.toMeasure bad ≤ ENNReal.ofReal
              (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ ω ∉ bad, ∀ theta : Vec d → ℝ,
              ContinuousOn theta B → (∀ x ∈ B, 0 < theta x) →
              (∀ ε' : ℝ, epsilonStar < ε' → ∃ b : ℝ, 0 < b ∧ ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ ε') →
              ∀ h : H1Function B, IsWeaklyHarmonicOn
                  (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M L ω x * theta x) B h →
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

end SubdiffusiveProcess.Paper
