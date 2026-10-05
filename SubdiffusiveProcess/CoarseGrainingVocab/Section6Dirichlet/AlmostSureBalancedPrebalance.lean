module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedSourcePrebalance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ResponseFiniteness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceEnergyPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceForcingPrice

@[expose] public section

/-!
# Almost-sure balanced Dirichlet prebalance

This file combines the source-normalized deterministic estimate with the
almost-sure response and energy rows.  The exceptional set is chosen before
the source and boundary data, as required by the cutoff Dirichlet theorem.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped _root_.ENNReal

noncomputable section

/-- The full optimizing-scale prebalance, simultaneously for every forcing,
boundary datum, and pair of weak solutions.  Its only probabilistic inputs
are finite positive moments of the two raw response errors. -/
theorem exists_ae_balancedCutoffDirichletPrebalance
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Ccg Cenergy : ℝ, 0 < Ccg ∧ 0 < Cenergy ∧
      ∀ (vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
        {p B1 B2 : ℝ}, 0 < p →
        paperENNRealLpNorm M.P.toMeasure p
            (fun omega ↦ paperHomogenizationError
              (originCube d (N : ℤ)) (N : ℤ) (dirichletS1 vartheta)
              .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L)) ≤
          ENNReal.ofReal B1 →
        paperENNRealLpNorm M.P.toMeasure p
            (fun omega ↦ paperHomogenizationError
              (originCube d (N : ℤ)) (N : ℤ) (dirichletS1 vartheta / 2)
              .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) ≤
          ENNReal.ofReal B2 →
        ∀ᵐ omega ∂M.P.toMeasure,
          ∀ (f : Vec d → ℝ)
            (hf : MemLp f 2
              (volume.restrict (openCubeSet (originCube d 0))))
            (h : H2Datum (originCube d 0))
            (u v : H1Function (openCubeSet (originCube d 0))),
            IsScalarDirichletSolutionOn
                (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                (originCube d 0) u h.toH1 f →
            IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                (originCube d 0) v h.toH1 f →
            paperNegativeFractionalDual (originCube d 0)
                  (dirichletSOrder vartheta hvartheta)
                  FiniteLpExponent.two
                  (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
                    (centeredCubeScale (N : ℤ))
                    (centeredCubeGradientDifferenceL2Field (N : ℤ)
                      (centeredCubeRawDilation (N : ℤ) u)
                      (centeredCubeRawDilation (N : ℤ) v))) +
                paperNegativeFractionalDual (originCube d 0)
                  (dirichletSOrder vartheta hvartheta)
                  FiniteLpExponent.two
                  (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
                    (centeredCubeScale (N : ℤ) * (ahom M L)⁻¹)
                    (centeredCubeFluxDifferenceL2Field (N : ℤ)
                      ((aCutoffFamily M L omega).coeffOn
                        (originCube d (N : ℤ)))
                      (ahom M L) (centeredCubeRawDilation (N : ℤ) u)
                      (centeredCubeRawDilation (N : ℤ) v))) ≤
              ENNReal.ofReal
                (dirichletUniversalRandomFactor M L N
                    (cutoffDirichletSourceCoefficient d Ccg Cenergy
                      vartheta hvartheta)
                    M.delta vartheta (dirichletS1 vartheta)
                    (dirichletS2 vartheta)
                    (dirichletBalanceScale vartheta M.delta) omega *
                  Real.rpow M.delta vartheta *
                    (‖toScalarL2 hf‖ + h.norm.toReal)) := by
  obtain ⟨Ccg, hCcg, hprebalance⟩ :=
    exists_cutoffDirichletSourcePrebalance d hd
  obtain ⟨Cenergy, hCenergy, henergy⟩ :=
    exists_ae_cutoffPhysicalDirichletEnergy_le_sourcePrice d
  refine ⟨Ccg, Cenergy, hCcg, hCenergy, ?_⟩
  intro vartheta hvartheta M L N p B1 B2 hp hOne hTwo
  let s1 := dirichletS1Order vartheta hvartheta
  let s := dirichletSOrder vartheta hvartheta
  let s2 := dirichletS2Order vartheta hvartheta
  let k := dirichletBalanceScale vartheta M.delta
  have hk : 0 < k := dirichletBalanceScale_pos hvartheta
    M.shellPrefix.delta_pos
    (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hs1s : (s1 : ℝ) < (s : ℝ) :=
    dirichletS1Order_lt_dirichletSOrder vartheta hvartheta
  have hss2 : (s : ℝ) < (s2 : ℝ) :=
    dirichletSOrder_lt_dirichletS2Order vartheta hvartheta
  have hs1s2 : (s1 : ℝ) < (s2 : ℝ) := hs1s.trans hss2
  have hraw := ae_rawDirichletResponses_eq_ofReal_readouts_of_moments
    M L N hp hOne hTwo
  have henergyAE := henergy M L N s1 s2 hs1s2 hp hTwo
  filter_upwards [hraw, henergyAE] with omega hrawOmega henergyOmega
  intro f hf h u v hu hv
  obtain ⟨F, hF, hbudget⟩ :=
    exists_unitDivergenceLift_with_real_budget d f hf
  have hsource : 0 ≤ ‖toScalarL2 hf‖ := norm_nonneg _
  have hpre := hprebalance (Cenergy := Cenergy) hCenergy.le
    M L N k hk omega s1 s s2 s1
    hs1s hss2 h F hu hv hF
    (dirichletFullResponseOne M L N (s1 : ℝ) omega)
    (dirichletFullResponseTwo M L N (s1 : ℝ) omega)
    ‖toScalarL2 hf‖
    (dirichletFullResponseOne_nonneg M L N (s1 : ℝ) omega)
    (dirichletFullResponseTwo_nonneg M L N (s1 : ℝ) omega)
    hsource
    (hrawOmega.1.trans_le le_rfl)
    (hrawOmega.2.trans_le le_rfl)
    (henergyOmega h F hu hF) hbudget
  have hcoefficient : 0 ≤
      cutoffDirichletSourceCoefficient d Ccg Cenergy vartheta hvartheta :=
    cutoffDirichletSourceCoefficient_nonneg d hvartheta hCcg.le hCenergy.le
  have hdatum : 0 ≤ ‖toScalarL2 hf‖ + h.norm.toReal :=
    add_nonneg hsource ENNReal.toReal_nonneg
  apply ENNReal.le_dirichletUniversalRandomFactor_of_prebalance
    M L N omega hcoefficient hdatum
  simpa only [s1, s, s2, k, dirichletS1Order_coe,
    dirichletSOrder_coe, dirichletS2Order_coe,
    cutoffDirichletSourceCoefficient] using hpre

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
