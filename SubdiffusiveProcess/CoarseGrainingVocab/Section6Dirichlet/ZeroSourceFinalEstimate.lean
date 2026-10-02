import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.AlmostSureZeroSourcePrebalance
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedFinalReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FinalRandomFactor

/-!
# Final zero-source cutoff Dirichlet estimate
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- A growth factor at least one can be moved outside the final deterministic
readout enlargement. -/
theorem dirichletReadoutRandomFactor_mul_le_mul
    (s : FractionalOrder) (d : ℕ) [NeZero d]
    {G U : ℝ} (hG : 1 ≤ G) :
    dirichletReadoutRandomFactor s d (G * U) ≤
      G * dirichletReadoutRandomFactor s d U := by
  unfold dirichletReadoutRandomFactor
  have hA : 0 ≤ (dirichletFinalReadoutConstant s d).toReal :=
    ENNReal.toReal_nonneg
  nlinarith

/-- The linear-in-`delta` zero-source estimate after the three literal final
readouts.  Its only additional deterministic price is the one-scale growth
factor `3^s₁`. -/
theorem exists_ae_zeroSourceCutoffDirichletFinalEstimate
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
            ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
              (∀ x, gradDifference.toFun x = u.grad x - v.grad x) ∧
              (∀ x, fluxDifference.toFun x =
                rescaledCutoffCoefficient M L N omega x • u.grad x - v.grad x) ∧
              l2Size (originCube d 0) (fun x ↦ u.toFun x - v.toFun x) +
                    ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                  ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                ENNReal.ofReal
                    (cutoffDirichletRandomFactor M L N
                        (cutoffDirichletSourceCoefficient d Ccg Cenergy
                          vartheta hvartheta)
                        vartheta hvartheta omega *
                      Real.rpow 3 (dirichletS1 vartheta) * M.delta) *
                  h.norm := by
  obtain ⟨Ccg, Cenergy, hCcg, hCenergy, hprebalance⟩ :=
    exists_ae_zeroSourceCutoffDirichletPrebalance d hd
  refine ⟨Ccg, Cenergy, hCcg, hCenergy, ?_⟩
  intro vartheta hvartheta M L N p B1 B2 hp hOne hTwo
  have hpreAE := hprebalance vartheta hvartheta M L N hp hOne hTwo
  filter_upwards [hpreAE] with omega hpreOmega
  intro h u v hu hv
  let U := dirichletUniversalRandomFactor M L N
    (cutoffDirichletSourceCoefficient d Ccg Cenergy vartheta hvartheta)
    M.delta vartheta (dirichletS1 vartheta) (dirichletS2 vartheta)
    (dirichletBalanceScale vartheta M.delta) omega
  let G := Real.rpow 3 (dirichletS1 vartheta)
  have hcoefficient : 0 ≤
      cutoffDirichletSourceCoefficient d Ccg Cenergy vartheta hvartheta :=
    cutoffDirichletSourceCoefficient_nonneg d hvartheta hCcg.le hCenergy.le
  have hU : 0 ≤ U := zero_le_one.trans
    (one_le_dirichletUniversalRandomFactor M L N hcoefficient
      M.shellPrefix.delta_pos.le vartheta (dirichletS1 vartheta)
      (dirichletS2 vartheta) (dirichletBalanceScale vartheta M.delta) omega)
  have hG : 1 ≤ G := by
    dsimp only [G]
    exact Real.one_le_rpow (by norm_num)
      (dirichlet_parameter_orders hvartheta.1 hvartheta.2).1.le
  have hpre := hpreOmega h u v hu hv
  have hfinal := exists_cutoffDirichletDifferenceFields_of_balancedPrebalance
    M L N omega (dirichletSOrder vartheta hvartheta) u v
    (hasH10Difference_of_scalarDirichletSolutions hu hv)
    (mul_nonneg (zero_le_one.trans hG) hU) M.shellPrefix.delta_pos.le
    ENNReal.toReal_nonneg hpre
  obtain ⟨gradDifference, fluxDifference, hgrad, hflux, hbound⟩ := hfinal
  refine ⟨gradDifference, fluxDifference, hgrad, hflux, hbound.trans ?_⟩
  rw [ENNReal.ofReal_toReal (h2Datum_norm_lt_top h).ne]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have hreadout := dirichletReadoutRandomFactor_mul_le_mul
    (dirichletSOrder vartheta hvartheta) d (U := U) hG
  have hdelta : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  calc
    dirichletReadoutRandomFactor (dirichletSOrder vartheta hvartheta) d
          (G * U) * M.delta ≤
        (G * dirichletReadoutRandomFactor
          (dirichletSOrder vartheta hvartheta) d U) * M.delta :=
      mul_le_mul_of_nonneg_right hreadout hdelta
    _ = cutoffDirichletRandomFactor M L N
          (cutoffDirichletSourceCoefficient d Ccg Cenergy vartheta hvartheta)
          vartheta hvartheta omega * G * M.delta := by
      dsimp only [U, G, cutoffDirichletRandomFactor]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
