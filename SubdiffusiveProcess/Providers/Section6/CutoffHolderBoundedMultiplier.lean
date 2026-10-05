module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.ConditionalOuterAssembly

@[expose] public section

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

theorem SubdiffusiveProcess.Providers.Section6.cutoff_holder_bounded_multiplier
    (d : ℕ) :
    ∃ epsilonStar c C : ℝ, 0 < epsilonStar ∧ 0 < c ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, (M.delta ≤ c → ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d, ∀ j : ℕ, 0 < j →
      let B := translatedCube d m z
      ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
        ∃ bad : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d),
          @MeasurableSet (_root_.SubdiffusiveProcess.Model.PotentialSample d)
              (⨆ i : ℕ, MeasurableSpace.comap
                (fun ω : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ ω i)
                inferInstance) bad ∧
          M.P.toMeasure bad ≤ ENNReal.ofReal
            (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
          ∀ ω ∉ bad, ∀ theta : Vec d → ℝ,
            ContinuousOn theta B → (∀ x ∈ B, 0 < theta x) →
            (∃ b > 0, ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilonStar) →
            ∀ h : H1Function B, IsWeaklyHarmonicOn
                (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M L ω x * theta x) B h →
              ∃ hRep : Vec d → ℝ,
                ContinuousOn hRep B ∧
                hRep =ᵐ[volume.restrict B] h.toFun ∧
                oscillationOn B' hRep ≤ C * (3 : ℝ) ^ (-c * j) *
                  oscillationOn {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8} hRep ∧
                sSup {r : ℝ | ∃ x ∈ B', r = |hRep x - averageOn B hRep|} ≤
                  C * normalizedL2On B
                    (fun x => hRep x - averageOn B hRep))
:=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.exists_boundedMultiplierEstimate d
