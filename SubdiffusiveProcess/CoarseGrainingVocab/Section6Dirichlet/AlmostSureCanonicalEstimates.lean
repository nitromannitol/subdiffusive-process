module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.AlmostSureBalancedPrebalance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.AlmostSureZeroSourcePrebalance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.CanonicalFinalReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FinalRandomFactor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ZeroSourceFinalEstimate

@[expose] public section

/-!
# Almost-sure estimates on the canonical Dirichlet difference fields
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The main `delta^vartheta` estimate with the canonical field witnesses
kept visible. -/
theorem exists_ae_cutoffDirichletCanonicalMainEstimate
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
          ∀ (f : Vec d → ℝ)
            (_hf : MemLp f 2
              (volume.restrict (openCubeSet (originCube d 0))))
            (h : H2Datum (originCube d 0))
            (u v : H1Function (openCubeSet (originCube d 0))),
            IsScalarDirichletSolutionOn
                (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                (originCube d 0) u h.toH1 f →
            IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                (originCube d 0) v h.toH1 f →
            l2Size (originCube d 0) (fun x ↦ u.toFun x - v.toFun x) +
                  ordinaryVectorHMinusOne (originCube d 0)
                    (cutoffDirichletGradientDifference N u v) +
                ordinaryVectorHMinusOne (originCube d 0)
                  (cutoffDirichletFluxDifference M L N omega u v) ≤
              ENNReal.ofReal
                  (cutoffDirichletRandomFactor M L N
                    (cutoffDirichletSourceCoefficient d Ccg Cenergy
                      vartheta hvartheta)
                    vartheta hvartheta omega * Real.rpow M.delta vartheta) *
                (l2Size (originCube d 0) f + h.norm) := by
  obtain ⟨Ccg, Cenergy, hCcg, hCenergy, hprebalance⟩ :=
    exists_ae_balancedCutoffDirichletPrebalance d hd
  refine ⟨Ccg, Cenergy, hCcg, hCenergy, ?_⟩
  intro vartheta hvartheta M L N p B1 B2 hp hOne hTwo
  filter_upwards [hprebalance vartheta hvartheta M L N hp hOne hTwo]
    with omega hpreOmega
  intro f _hf h u v hu hv
  let U := dirichletUniversalRandomFactor M L N
    (cutoffDirichletSourceCoefficient d Ccg Cenergy vartheta hvartheta)
    M.delta vartheta (dirichletS1 vartheta) (dirichletS2 vartheta)
    (dirichletBalanceScale vartheta M.delta) omega
  let T := Real.rpow M.delta vartheta
  let D := ‖toScalarL2 _hf‖ + h.norm.toReal
  have hU : 0 ≤ U := zero_le_one.trans
    (one_le_dirichletUniversalRandomFactor M L N
      (cutoffDirichletSourceCoefficient_nonneg d hvartheta
        hCcg.le hCenergy.le)
      M.shellPrefix.delta_pos.le vartheta (dirichletS1 vartheta)
      (dirichletS2 vartheta) (dirichletBalanceScale vartheta M.delta) omega)
  have hT : 0 ≤ T := Real.rpow_nonneg M.shellPrefix.delta_pos.le _
  have hD : 0 ≤ D := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hfinal := cutoffDirichletCanonicalDifferenceFields_le_of_balancedPrebalance
    M L N omega (dirichletSOrder vartheta hvartheta) u v
    (hasH10Difference_of_scalarDirichletSolutions hu hv)
    hU hT hD (hpreOmega f _hf h u v hu hv)
  simpa only [U, T, D, cutoffDirichletRandomFactor,
    ofReal_norm_toScalarL2_add_h2DatumNorm_toReal] using hfinal

/-- The zero-source linear estimate on the same canonical field witnesses. -/
theorem exists_ae_cutoffDirichletCanonicalZeroSourceEstimate
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
            l2Size (originCube d 0) (fun x ↦ u.toFun x - v.toFun x) +
                  ordinaryVectorHMinusOne (originCube d 0)
                    (cutoffDirichletGradientDifference N u v) +
                ordinaryVectorHMinusOne (originCube d 0)
                  (cutoffDirichletFluxDifference M L N omega u v) ≤
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
  filter_upwards [hprebalance vartheta hvartheta M L N hp hOne hTwo]
    with omega hpreOmega
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
  have hcanonical := cutoffDirichletCanonicalDifferenceFields_le_of_balancedPrebalance
    M L N omega (dirichletSOrder vartheta hvartheta) u v
    (hasH10Difference_of_scalarDirichletSolutions hu hv)
    (mul_nonneg (zero_le_one.trans hG) hU) M.shellPrefix.delta_pos.le
    ENNReal.toReal_nonneg (hpreOmega h u v hu hv)
  rw [ENNReal.ofReal_toReal (h2Datum_norm_lt_top h).ne] at hcanonical
  refine hcanonical.trans ?_
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have hreadout := dirichletReadoutRandomFactor_mul_le_mul
    (dirichletSOrder vartheta hvartheta) d (U := U) hG
  calc
    dirichletReadoutRandomFactor (dirichletSOrder vartheta hvartheta) d
          (G * U) * M.delta ≤
        (G * dirichletReadoutRandomFactor
          (dirichletSOrder vartheta hvartheta) d U) * M.delta :=
      mul_le_mul_of_nonneg_right hreadout M.shellPrefix.delta_pos.le
    _ = cutoffDirichletRandomFactor M L N
          (cutoffDirichletSourceCoefficient d Ccg Cenergy vartheta hvartheta)
          vartheta hvartheta omega * G * M.delta := by
      dsimp only [U, G, cutoffDirichletRandomFactor]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
