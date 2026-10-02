import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePrebalanceThreshold
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourcePrebalanceComposition
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceEnergyPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedFinalReadout
set_option autoImplicit false
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A deterministic response threshold gives a uniform Dirichlet comparison at all cutoff scales. -/
theorem exists_goodCube_dirichlet_comparison_threshold
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (eps : ℝ) (heps : 0 < eps) :
    ∃ zeta : ℝ, 0 < zeta ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
        {p B : ℝ}, 0 < p →
        paperENNRealLpNorm M.P.toMeasure p
          (fun omega => paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
            (1 / 8) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) ≤
          ENNReal.ofReal B →
        ∀ᵐ omega ∂M.P.toMeasure,
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
              (1 / 4) .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal zeta →
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
              (1 / 8) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal zeta →
          ∀ (f : Vec d → ℝ)
            (_hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))))
            (h : H2Datum (originCube d 0))
            (u v : H1Function (openCubeSet (originCube d 0))),
            IsScalarDirichletSolutionOn
              (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
              (originCube d 0) u h.toH1 f →
            IsScalarDirichletSolutionOn (fun _ => (1 : Mat d))
              (originCube d 0) v h.toH1 f →
            l2Size (originCube d 0) (fun x => u.toFun x - v.toFun x) ≤
              ENNReal.ofReal eps * (l2Size (originCube d 0) f + h.norm) := by
  obtain ⟨Ccg, hCcg, hpre⟩ := exists_cutoffDirichletSourcePrebalance d hd
  obtain ⟨Cenergy, hCenergy, hae⟩ :=
    exists_ae_cutoffPhysicalDirichletEnergy_le_sourcePrice d
  obtain ⟨s1, s, s2, hs1v, hsv, hs2v⟩ :
      ∃ a b c : FractionalOrder,
        a.1 = (1 / 4 : ℝ) ∧ b.1 = (1 / 2 : ℝ) ∧ c.1 = (3 / 4 : ℝ) :=
    ⟨⟨(1/4 : ℝ), by norm_num⟩, ⟨(1/2 : ℝ), by norm_num⟩, ⟨(3/4 : ℝ), by norm_num⟩,
      rfl, rfl, rfl⟩
  have hs1pos : 0 < s1.1 := by rw [hs1v]; norm_num
  have hspos : 0 < s.1 := by rw [hsv]; norm_num
  have hs2pos : 0 < s2.1 := by rw [hs2v]; norm_num
  have h11 : s1.1 < s.1 := by rw [hs1v, hsv]; norm_num
  have h1s2 : s.1 < s2.1 := by rw [hsv, hs2v]; norm_num
  have h12 : s1.1 < s2.1 := by rw [hs1v, hs2v]; norm_num
  have hq : s1.1 / 2 = (1 / 8 : ℝ) := by rw [hs1v]; norm_num
  have hCs0 : 0 ≤ sourceDirichletPrebalanceConstant Ccg s.1 s2.1
      (dirichletWeightedEnergyFactor s1.1 s.1)
      (sourceDirichletEnergyConstant d Cenergy s1)
      (sourceDirichletFractionalDatumConstant d s2) :=
    sourceDirichletPrebalanceConstant_nonneg (le_of_lt hCcg) hspos h1s2
      (dirichletWeightedEnergyFactor_nonneg _ _)
      (sourceDirichletEnergyConstant_nonneg d (le_of_lt hCenergy) s1)
      (sourceDirichletFractionalDatumConstant_nonneg d s2)
  have hCr0 : 0 ≤ (dirichletFinalReadoutConstant s d).toReal := ENNReal.toReal_nonneg
  have hCC0 : 0 ≤ (dirichletFinalReadoutConstant s d).toReal *
      (sourceDirichletPrebalanceConstant Ccg s.1 s2.1
        (dirichletWeightedEnergyFactor s1.1 s.1)
        (sourceDirichletEnergyConstant d Cenergy s1)
        (sourceDirichletFractionalDatumConstant d s2)) := mul_nonneg hCr0 hCs0
  have hCbig : 0 < 1 + (dirichletFinalReadoutConstant s d).toReal *
      (sourceDirichletPrebalanceConstant Ccg s.1 s2.1
        (dirichletWeightedEnergyFactor s1.1 s.1)
        (sourceDirichletEnergyConstant d Cenergy s1)
        (sourceDirichletFractionalDatumConstant d s2)) := by linarith
  obtain ⟨k, zeta, hk, hzeta, hzeta1, hcore⟩ :=
    goodCube_exists_fixed_prebalance_threshold s1.1 s2.1
      (1 + (dirichletFinalReadoutConstant s d).toReal *
        (sourceDirichletPrebalanceConstant Ccg s.1 s2.1
          (dirichletWeightedEnergyFactor s1.1 s.1)
          (sourceDirichletEnergyConstant d Cenergy s1)
          (sourceDirichletFractionalDatumConstant d s2))) eps hs2pos hCbig heps
  have hofReal_le : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      ENNReal.ofReal x ≤ ENNReal.ofReal y → x ≤ y := by
    intro x y hx hy h
    have h1 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top).2 h
    rwa [ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal hy] at h1
  have key1 : ∀ x : ENNReal, x ≤ ENNReal.ofReal zeta →
      ∃ E : ℝ, 0 ≤ E ∧ E ≤ zeta ∧ x = ENNReal.ofReal E := by
    intro x hx
    have hfin : x ≠ ⊤ := by
      intro hc
      rw [hc] at hx
      exact ENNReal.ofReal_ne_top (le_antisymm hx le_top).symm
    refine ⟨x.toReal, ENNReal.toReal_nonneg, ?_, (ENNReal.ofReal_toReal hfin).symm⟩
    refine hofReal_le x.toReal zeta ENNReal.toReal_nonneg (le_of_lt hzeta) ?_
    rw [← (ENNReal.ofReal_toReal hfin).symm]
    exact hx
  refine ⟨zeta, hzeta, ?_⟩
  intro M L N p B hp hnorm
  have hnorm' : paperENNRealLpNorm M.P.toMeasure p
      (fun omega => paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        (s1.1 / 2) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) ≤
    ENNReal.ofReal B := by rw [hq]; exact hnorm
  filter_upwards [hae M L N s1 s2 h12 hp hnorm'] with omega haeo
  intro h1 h2
  obtain ⟨E1, hE10, hE1z, h1eq⟩ := key1
    (paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) (1 / 4) .infinity
      (.finite 1) (aCutoffFamily M L omega) (ahom M L)) h1
  obtain ⟨E2, hE20, hE2z, h2eq⟩ := key1
    (paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) (1 / 8) .infinity
      (.finite 2) (aCutoffFamily M L omega) (ahom M L)) h2
  have h1le : paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) s1.1
      .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L) ≤
    ENNReal.ofReal E1 := by rw [hs1v]; exact le_of_eq h1eq
  have h2le : paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) (s1.1 / 2)
      .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L) ≤
    ENNReal.ofReal E2 := by rw [hq]; exact le_of_eq h2eq
  have henv : dirichletEllipticityEnvelope M L N s1.1 omega = 1 + 2 * E2 := by
    unfold dirichletEllipticityEnvelope dirichletFullResponseTwo
    rw [hq, h2eq, ENNReal.toReal_ofReal hE20]
  intro f hf h u v hu hv
  obtain ⟨F, hF, hbudget⟩ := exists_unitDivergenceLift_with_real_budget d f hf
  have henergy := haeo h F hu hF
  have hpb := hpre (Cenergy := Cenergy) (le_of_lt hCenergy) M L N k hk omega s1 s s2 s1
    h11 h1s2 h F hu hv hF
  have hpb2 := hpb E1 E2 (‖toScalarL2 hf‖) hE10 hE20 (norm_nonneg _) h1le h2le
    henergy hbudget
  rw [henv] at hpb2
  set Cs := sourceDirichletPrebalanceConstant Ccg s.1 s2.1
      (dirichletWeightedEnergyFactor s1.1 s.1)
      (sourceDirichletEnergyConstant d Cenergy s1)
      (sourceDirichletFractionalDatumConstant d s2) with hCsdef
  set core := dirichletPrebalanceCore s1.1 s2.1 k E1 E2 (1 + 2 * E2) with hcoredef
  have hCCle : (dirichletFinalReadoutConstant s d).toReal * Cs ≤
      1 + (dirichletFinalReadoutConstant s d).toReal * Cs := by linarith
  have hsum1 : l2Size (originCube d 0) (fun x => u.toFun x - v.toFun x) ≤
      l2Size (originCube d 0) (fun x => u.toFun x - v.toFun x) +
        ordinaryVectorHMinusOne (originCube d 0)
          (cutoffDirichletGradientDifference N u v) +
        ordinaryVectorHMinusOne (originCube d 0)
          (cutoffDirichletFluxDifference M L N omega u v) :=
    le_add_right (le_add_right (le_refl _))
  have hread := dirichletFinalReadout_le_paperNegativeFractionalDual_sum s u v
    (cutoffDirichletGradientDifference N u v)
    (cutoffDirichletFluxDifference M L N omega u v)
    (cutoffDirichletGradientDifference_toFun N u v)
    (hasH10Difference_of_scalarDirichletSolutions hu hv)
  rw [cutoffDirichletDifferenceFields_paperDual_sum_eq M L N omega s u v] at hread
  have hsum2 := le_trans hread (mul_le_mul_right hpb2 (dirichletFinalReadoutConstant s d))
  have hCre : dirichletFinalReadoutConstant s d =
      ENNReal.ofReal (dirichletFinalReadoutConstant s d).toReal :=
    (ENNReal.ofReal_toReal (ne_of_lt (dirichletFinalReadoutConstant_lt_top s d))).symm
  have hA : (dirichletFinalReadoutConstant s d).toReal * Cs * core ≤ eps := by
    rcases le_or_gt 0 core with hc | hc
    · refine le_trans (mul_le_mul_of_nonneg_right hCCle hc) ?_
      rw [hcoredef]
      exact hcore E1 E2 hE10 hE20 hE1z hE2z
    · have hneg : (dirichletFinalReadoutConstant s d).toReal * Cs * core ≤ 0 := by
        nlinarith [hCC0, hc, hCr0, hCs0]
      exact le_trans hneg (le_of_lt heps)
  have hkey : (dirichletFinalReadoutConstant s d).toReal *
        (Cs * core * (‖toScalarL2 hf‖ + h.norm.toReal)) ≤
      eps * (‖toScalarL2 hf‖ + h.norm.toReal) := by
    have hD0 : 0 ≤ ‖toScalarL2 hf‖ + h.norm.toReal :=
      add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
    calc (dirichletFinalReadoutConstant s d).toReal *
        (Cs * core * (‖toScalarL2 hf‖ + h.norm.toReal)) =
        ((dirichletFinalReadoutConstant s d).toReal * Cs * core) *
          (‖toScalarL2 hf‖ + h.norm.toReal) := by ring
      _ ≤ eps * (‖toScalarL2 hf‖ + h.norm.toReal) :=
          mul_le_mul_of_nonneg_right hA hD0
  have hfin : l2Size (originCube d 0) (fun x => u.toFun x - v.toFun x) ≤
      ENNReal.ofReal (eps * (‖toScalarL2 hf‖ + h.norm.toReal)) := by
    refine le_trans (le_trans hsum1 hsum2) ?_
    rw [hCre, ← ENNReal.ofReal_mul hCr0]
    exact ENNReal.ofReal_le_ofReal hkey
  simpa only [ENNReal.ofReal_mul heps.le,
    ofReal_norm_toScalarL2_add_h2DatumNorm_toReal f hf h] using hfin

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
