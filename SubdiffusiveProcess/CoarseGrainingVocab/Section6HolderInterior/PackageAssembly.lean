module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GammaOneComposition
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowsAboveCutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.UncutGammaOneTail

@[expose] public section

/-!
# The package assembly: one carrier, one constant, and the `L < m` residual

The frozen interior anchor's first conjunct is stated for **every** pair `(L, m)`
with no relation between them; only its second conjunct carries the guard
`m ≤ L`.  This module performs the assembly and isolates exactly what is
missing.

## One carrier for both packages

The frozen conjuncts only ask for *some* measurable `X`; nothing forces the
fixed-cutoff witness to be the finite-cutoff stopping carrier.  Taking the
**cutoff-independent** carrier `Section6Stopping.measurableHolderStoppingScale`
for both packages has two effects: the two Γ₁ obligations collapse into the one
that is already a theorem (`exists_uncutGammaOneTail`), and the `(some L)`
versus `none` mismatch between
`Section6Stopping.measurableCutoffHolderStoppingScale` and the established rows
disappears entirely.

## The residual

`InteriorRowsBelowCutoff` is the `L < m` sub-case of the three rows, i.e. the
second half of the printed proof of `p.cutoff.Holder.regularity`
(`p.cutoff.Holder.regularity` and `p.Holder.regularity` and `l.excess.decay.good.scales.GMC` and `l.cutoff.regularity.good.scale.estimates`, "If `L ≥ m` this is Proposition
`p.Holder.regularity`; we may therefore suppose `L < m`").  It is **not**
derivable from `InteriorHolderExcessDecayInput`: that premise is the interior
branch of the draft `l.excess.decay.good.scales.GMC` (:7435), whose binder list
contains `m ≤ L`, so it cannot be instantiated at `L < m` at all; and its good
event is `goodEvent M none (n+2) z`, which for `n + 2 > L` differs from
`goodEvent M (some L) (n+2) z`.  The printed proof uses a *different* lemma for
this branch — `l.cutoff.regularity.good.scale.estimates`, "in the
setting of Lemma `l.excess.decay.good.scales.GMC`, with its hypothesis `L ≥ m`
removed, its conclusion holds with `𝒢_{n+2,z}` replaced by `𝒢^{(L)}_{n+2,z}`" —
which is not among the thirteen frozen §6 anchors.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The three frozen interior rows at the cutoff-independent stopping carrier,
for **every** cutoff `L` and domain scale `m`. -/
def InteriorRowsAllCutoffsAt (d : ℕ) (C C1 C2 : ℝ) (step : ℕ) : Prop :=
  ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ L m : ℕ, ∀ ω,
        ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
          IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
              (cube d m) u g →
          MemHolder (cube d m) (1 / 2) g →
          InteriorHolderRegularityConclusions M C L ω alpha m
            (Section6Stopping.measurableHolderStoppingScale M alpha
              (Section6Stopping.holderStoppingLambda C1 alpha)
              (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω) u g

/-- **The `L < m` sub-case of the three frozen interior rows.**  See the module
docstring: this is `l.cutoff.regularity.good.scale.estimates`. -/
def InteriorRowsBelowCutoff (d : ℕ) : Prop :=
  ∀ C1 C2 : ℝ, 2 ≤ C1 → C1 ≤ C2 → ∀ step : ℕ, 21 ≤ step →
    ∃ Cmin : ℝ, 0 ≤ Cmin ∧ ∀ C : ℝ, Cmin ≤ C →
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
      ∀ L m : ℕ, L < m →
      ∀ ω : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
            (cube d m) u g →
        MemHolder (cube d m) (1 / 2) g →
        InteriorHolderRegularityConclusions M C L ω alpha m
          (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω) u g

/-- The fixed-cutoff sample-space package, at the cutoff-independent carrier. -/
theorem interiorCutoffPathwiseInput_of_uncutTailAndRows {C C1 C2 : ℝ} {step : ℕ}
    (htail : UncutGammaOneTailAt d C C1 C2 step)
    (hrows : InteriorRowsAllCutoffsAt d C C1 C2 step) :
    InteriorCutoffPathwiseInput d C := by
  intro M hdelta alpha halpha L m
  exact ⟨Section6Stopping.measurableHolderStoppingScale M alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m,
    Section6Stopping.measurable_measurableHolderStoppingScale _ _ _ _ _ _,
    fun ω => Section6Stopping.measurableHolderStoppingScale_pos _ _ _ _ _ _ ω,
    fun k hk => htail M hdelta alpha halpha m k hk,
    fun ω u g hsol hg => hrows M hdelta alpha halpha L m ω u g hsol hg⟩

/-- The cutoff-uniform sample-space package, at the same carrier. -/
theorem interiorCutoffUniformInput_of_uncutTailAndRows {C C1 C2 : ℝ} {step : ℕ}
    (htail : UncutGammaOneTailAt d C C1 C2 step)
    (hrows : InteriorRowsAllCutoffsAt d C C1 C2 step) :
    InteriorCutoffUniformInput d C := by
  intro M hdelta alpha halpha m
  exact ⟨Section6Stopping.measurableHolderStoppingScale M alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m,
    Section6Stopping.measurable_measurableHolderStoppingScale _ _ _ _ _ _,
    fun ω => Section6Stopping.measurableHolderStoppingScale_pos _ _ _ _ _ _ ω,
    fun k hk => htail M hdelta alpha halpha m k hk,
    fun _ _ ω u g hsol hg => hrows M hdelta alpha halpha _ m ω u g hsol hg⟩

/-- **The rows at every cutoff, from the two branches.**  The `m ≤ L` branch is
`RowsAboveCutoff.exists_interiorRowsAboveCutoff`; the `L < m` branch is the
residual `InteriorRowsBelowCutoff`. -/
theorem exists_interiorRowsAllCutoffs (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d)
    (hbelow : InteriorRowsBelowCutoff d) :
    ∃ C0 C1 C2 : ℝ, 0 < C0 ∧ 1 ≤ C1 ∧ 1 ≤ C2 ∧
      ∀ C : ℝ, C0 ≤ C → InteriorRowsAllCutoffsAt d C C1 C2 21 := by
  classical
  obtain ⟨C1, C2, CminA, hC1two, hC1C2, hCminA, habove⟩ :=
    exists_interiorRowsAboveCutoff d hExcess
  obtain ⟨CminB, hCminB, hbelowAt⟩ := hbelow C1 C2 hC1two hC1C2 21 le_rfl
  have hC1one : (1 : ℝ) ≤ C1 := by linarith
  have hC2one : (1 : ℝ) ≤ C2 := by linarith
  refine ⟨max (max 46 C1) (max (1024 * C2 ^ 2) (max CminA CminB)), C1, C2, ?_,
    hC1one, hC2one, ?_⟩
  · exact lt_of_lt_of_le (by norm_num)
      (le_trans (le_max_left (46 : ℝ) C1) (le_max_left _ _))
  intro C hC0 M hdelta alpha halpha L m ω u g hsol hg
  have h46 : (46 : ℝ) ≤ C :=
    le_trans (le_trans (le_max_left (46 : ℝ) C1) (le_max_left _ _)) hC0
  have hCC1 : C1 ≤ C :=
    le_trans (le_trans (le_max_right (46 : ℝ) C1) (le_max_left _ _)) hC0
  have hCC2 : 1024 * C2 ^ 2 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC0
  have hCA : CminA ≤ C :=
    le_trans (le_trans (le_max_left CminA CminB)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hC0
  have hCB : CminB ≤ C :=
    le_trans (le_trans (le_max_right CminA CminB)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hC0
  obtain ⟨hsmall, halphaIcc, hepsIcc, hlamdelta⟩ :=
    holderStopping_model_conditions M hC1one hC2one h46 hCC1 hCC2 hdelta halpha
  rcases le_or_gt m L with hmL | hLm
  · exact habove C hCA 21 le_rfl M hsmall alpha halphaIcc hepsIcc hlamdelta
      L m hmL ω u g hsol hg
  · exact hbelowAt C hCB M hsmall alpha halphaIcc hepsIcc hlamdelta L m hLm
      ω u g hsol hg

/-- **The frozen interior anchor, conditional on the excess-decay premise and
the `L < m` residual.** -/
theorem exists_cutoffHolderRegularityInterior_of_excess_and_below (d : ℕ)
    [NeZero d] (hExcess : InteriorHolderExcessDecayInput d)
    (hbelow : InteriorRowsBelowCutoff d) :
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
  obtain ⟨C0, C1, C2, hC0, hC1, hC2, hrows⟩ :=
    exists_interiorRowsAllCutoffs d hExcess hbelow
  obtain ⟨Ct, hCt, htail⟩ := exists_uncutGammaOneTail d 21 hC1 hC2
  have hCpos : 0 < max Ct C0 := lt_of_lt_of_le hCt (le_max_left _ _)
  have htailMax := uncutGammaOneTailAt_mono hCt (le_max_left Ct C0) htail
  have hrowsMax := hrows (max Ct C0) (le_max_right _ _)
  exact exists_cutoffHolderRegularityInterior_of_inputs d _ hCpos
    (interiorCutoffPathwiseInput_of_uncutTailAndRows htailMax hrowsMax)
    (interiorCutoffUniformInput_of_uncutTailAndRows htailMax hrowsMax)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
