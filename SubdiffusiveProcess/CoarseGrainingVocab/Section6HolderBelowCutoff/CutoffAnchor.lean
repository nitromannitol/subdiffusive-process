module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.CutoffRowsAt
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.UncutRowsAtFree

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The interior anchor from the two interior excess-decay premises.**
No row obligation is left: the `L < m` branch runs at the manuscript's own
cutoff stopping scale. -/
theorem exists_cutoffHolderRegularityInterior_of_excessPair (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d)
    (hExcessCut : InteriorCutoffHolderExcessDecayInput d (-2 : ℝ) (-8 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ L m : ℕ,
          (∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
                  (cube d m) u g →
              MemHolder (cube d m) (1 / 2) g →
              InteriorHolderRegularityConclusions M C L ω alpha m (X ω) u g) ∧
          (m ≤ L → ∃ Xuncut : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C J ω alpha m (Xuncut ω) u g) ∧
          ∀ y : Vec d,
            (∃ Xy : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn
                    (_root_.SubdiffusiveProcess.Model.aCutoff M L
                      (translatePotentialSample y ω))
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C L (translatePotentialSample y ω)
                  alpha m (Xy ω) u g) ∧
            (m ≤ L → ∃ XuncutY : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable XuncutY ∧ (∀ ω, 0 < XuncutY ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < XuncutY ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDivFormWeakSolutionOn
                      (_root_.SubdiffusiveProcess.Model.aCutoff M J
                        (translatePotentialSample y ω))
                      (cube d m) u g →
                  MemHolder (cube d m) (1 / 2) g →
                  InteriorHolderRegularityConclusions M C J (translatePotentialSample y ω)
                    alpha m (XuncutY ω) u g)) := by
  classical
  obtain ⟨A1, A2, ACmin, hA1two, hA1A2, hACmin, huncut⟩ :=
    Rows.exists_interiorUncutRowsAt_free d hExcess
  obtain ⟨B1, B2, BCmin, hB1two, hB1B2, hBCmin, hcut⟩ :=
    Rows.exists_interiorCutoffRowsAt_of_cutoffExcess d hExcessCut
  set C1 : ℝ := max A1 B1 with hC1def
  set C2 : ℝ := max (max A2 B2) C1 with hC2def
  have hA1C1 : A1 ≤ C1 := le_max_left _ _
  have hB1C1 : B1 ≤ C1 := le_max_right _ _
  have hA2C2 : A2 ≤ C2 := le_trans (le_max_left A2 B2) (le_max_left _ _)
  have hB2C2 : B2 ≤ C2 := le_trans (le_max_right A2 B2) (le_max_left _ _)
  have hC1C2 : C1 ≤ C2 := le_max_right _ _
  have hC1two : (2 : ℝ) ≤ C1 := le_trans hA1two hA1C1
  have hC1one : (1 : ℝ) ≤ C1 := by linarith
  have hC2one : (1 : ℝ) ≤ C2 := by linarith
  refine exists_cutoffHolderRegularityInterior_of_rows d 21
    (C0 := max (max 46 C1) (max (1024 * C2 ^ 2) (max ACmin BCmin)))
    hC1one hC2one ?_ ?_
  · intro C hC0 M hdelta alpha halpha L m ω u g hsol hg
    have h46 : (46 : ℝ) ≤ C :=
      le_trans (le_trans (le_max_left (46 : ℝ) C1) (le_max_left _ _)) hC0
    have hCC1 : C1 ≤ C :=
      le_trans (le_trans (le_max_right (46 : ℝ) C1) (le_max_left _ _)) hC0
    have hCC2 : 1024 * C2 ^ 2 ≤ C :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC0
    have hCB : BCmin ≤ C :=
      le_trans (le_trans (le_max_right ACmin BCmin)
        (le_trans (le_max_right _ _) (le_max_right _ _))) hC0
    obtain ⟨hsmall, halphaIcc, hepsIcc, hlamdelta⟩ :=
      holderStopping_model_conditions M hC1one hC2one h46 hCC1 hCC2 hdelta halpha
    exact hcut C1 C2 hB1C1 hB2C2 hC1C2 C hCB 21 le_rfl M hsmall alpha halphaIcc
      hepsIcc hlamdelta L m ω u g hsol hg
  · intro C hC0 M hdelta alpha halpha m J hJ ω u g hsol hg
    have h46 : (46 : ℝ) ≤ C :=
      le_trans (le_trans (le_max_left (46 : ℝ) C1) (le_max_left _ _)) hC0
    have hCC1 : C1 ≤ C :=
      le_trans (le_trans (le_max_right (46 : ℝ) C1) (le_max_left _ _)) hC0
    have hCC2 : 1024 * C2 ^ 2 ≤ C :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC0
    have hCA : ACmin ≤ C :=
      le_trans (le_trans (le_max_left ACmin BCmin)
        (le_trans (le_max_right _ _) (le_max_right _ _))) hC0
    obtain ⟨hsmall, halphaIcc, hepsIcc, hlamdelta⟩ :=
      holderStopping_model_conditions M hC1one hC2one h46 hCC1 hCC2 hdelta halpha
    exact huncut C1 C2 hA1C1 hA2C2 hC1C2 C hCA 21 le_rfl M hsmall alpha halphaIcc
      hepsIcc hlamdelta J m hJ ω u g hsol hg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
