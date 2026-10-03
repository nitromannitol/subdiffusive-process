module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedSourcePrebalance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ResponseFiniteness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceEnergyPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ZeroSourcePrebalance

@[expose] public section

/-!
# Almost-sure zero-source Dirichlet prebalance

This is the linear-in-`delta` companion to the balanced source estimate.  It
uses the same universal response factor, but coarse grains at one physical
scale before comparing with the optimizing-scale factor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- Almost surely, every pair of zero-source solutions satisfies the
linear-in-`delta` negative-dual prebalance, uniformly in the boundary datum.
The optimizing scale occurs only in the universal random factor. -/
theorem exists_ae_zeroSourceCutoffDirichletPrebalance
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Ccg Cenergy : ℝ, 0 < Ccg ∧ 0 < Cenergy ∧
      ∀ (vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1)
        (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
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
          ∀ (h : H2Datum (originCube d 0))
            (u v : H1Function (openCubeSet (originCube d 0))),
            IsScalarDirichletSolutionOn
                (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                (originCube d 0) u h.toH1 0 →
            IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                (originCube d 0) v h.toH1 0 →
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
                (Real.rpow 3 (dirichletS1 vartheta) *
                  dirichletUniversalRandomFactor M L N
                    (cutoffDirichletSourceCoefficient d Ccg Cenergy
                      vartheta hvartheta)
                    M.delta vartheta (dirichletS1 vartheta)
                    (dirichletS2 vartheta)
                    (dirichletBalanceScale vartheta M.delta) omega *
                  M.delta * h.norm.toReal) := by
  obtain ⟨Ccg, hCcg, hprebalance⟩ :=
    exists_cutoffDirichletZeroSourcePrebalance d hd
  obtain ⟨Cenergy, hCenergy, henergy⟩ :=
    exists_ae_cutoffPhysicalDirichletEnergy_le_sourcePrice d
  refine ⟨Ccg, Cenergy, hCcg, hCenergy, ?_⟩
  intro vartheta hvartheta M L N p B1 B2 hp hOne hTwo
  let s1 := dirichletS1Order vartheta hvartheta
  let s := dirichletSOrder vartheta hvartheta
  let s2 := dirichletS2Order vartheta hvartheta
  let k := dirichletBalanceScale vartheta M.delta
  have hs1s : (s1 : ℝ) < (s : ℝ) :=
    dirichletS1Order_lt_dirichletSOrder vartheta hvartheta
  have hss2 : (s : ℝ) < (s2 : ℝ) :=
    dirichletSOrder_lt_dirichletS2Order vartheta hvartheta
  have hs1s2 : (s1 : ℝ) < (s2 : ℝ) := hs1s.trans hss2
  have hraw := ae_rawDirichletResponses_eq_ofReal_readouts_of_moments
    M L N hp hOne hTwo
  have henergyAE := henergy M L N s1 s2 hs1s2 hp hTwo
  filter_upwards [hraw, henergyAE] with omega hrawOmega henergyOmega
  intro h u v hu hv
  let E1 := dirichletFullResponseOne M L N (s1 : ℝ) omega
  let E2 := dirichletFullResponseTwo M L N (s1 : ℝ) omega
  let Y := dirichletEllipticityEnvelope M L N (s1 : ℝ) omega
  let C := cutoffDirichletSourceCoefficient d Ccg Cenergy
    vartheta hvartheta
  have hE1 : 0 ≤ E1 := dirichletFullResponseOne_nonneg M L N (s1 : ℝ) omega
  have hE2 : 0 ≤ E2 := dirichletFullResponseTwo_nonneg M L N (s1 : ℝ) omega
  have hY : 0 ≤ Y := zero_le_one.trans
    (one_le_dirichletEllipticityEnvelope M L N (s1 : ℝ) omega)
  have hC : 0 ≤ C :=
    cutoffDirichletSourceCoefficient_nonneg d hvartheta hCcg.le hCenergy.le
  have hpre := hprebalance (Cenergy := Cenergy) hCenergy.le
    M L N omega s1 s s2 s1 hs1s hss2 h hu hv
    (fun F hF ↦ henergyOmega h F hu hF)
    E1 E2 hE1 hE2
    (hrawOmega.1.trans_le le_rfl) (hrawOmega.2.trans_le le_rfl)
  have hlinear := mul_growth_one_mul_response_mul_le_randomFactor_mul_delta_mul
    (C := C) (delta := M.delta) (vartheta := vartheta)
    (s1 := (s1 : ℝ)) (s2 := (s2 : ℝ)) (E1 := E1) (E2 := E2)
    (Y := Y) (D := h.norm.toReal) (k := k)
    hC M.shellPrefix.delta_pos hE1 hY ENNReal.toReal_nonneg
  refine hpre.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    sourceDirichletPrebalanceConstant Ccg (s : ℝ) (s2 : ℝ)
          (dirichletWeightedEnergyFactor (s1 : ℝ) (s : ℝ))
          (sourceDirichletEnergyConstant d Cenergy s1)
          (sourceDirichletFractionalDatumConstant d s2) *
        (Real.rpow 3 (s1 : ℝ) * E1 * Y) * h.norm.toReal =
        C * Real.rpow 3 (s1 : ℝ) * E1 * Y * h.norm.toReal := by
          dsimp only [C, cutoffDirichletSourceCoefficient]
          simp only [s1, s, s2, dirichletS1Order_coe,
            dirichletSOrder_coe, dirichletS2Order_coe]
          ring
    _ ≤ Real.rpow 3 (s1 : ℝ) *
        dirichletRandomFactor C M.delta vartheta (s1 : ℝ) (s2 : ℝ) k
          (fun _ : Unit ↦ E1) (fun _ : Unit ↦ E2)
          (fun _ : Unit ↦ Y) () * M.delta * h.norm.toReal := hlinear
    _ = _ := by
      simp only [s1, s2, k, E1, E2, Y, C,
        dirichletS1Order_coe, dirichletS2Order_coe]
      rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
