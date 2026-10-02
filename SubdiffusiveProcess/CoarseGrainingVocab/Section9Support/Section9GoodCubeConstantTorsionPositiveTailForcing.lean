import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeUnitTorsion
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepConcreteCellCarrier
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePositiveScaleTail
/-!

The raw cutoff supplies the ellipticity, square-integrability and exact Besov carriers required by the forcing comparison. A dimensional Besov tolerance absorbs the forcing error using the coarse lambda price.
-/

set_option autoImplicit false
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Section9
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Choose a dimensional raw Besov tolerance that pays the weighted-forcing error. -/
theorem exists_goodCube_cutoff_torsion_comparison_tolerance
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (eps : ℝ) (heps : 0 < eps) :
    ∃ zeta : ℝ, 0 < zeta ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d),
        ahom M L * (Ch02.lambdaSq Q (1 / 2) (.finite 1)
          (aCutoffFamily M L omega))⁻¹ ≤ 9 →
        (∀ hf : ExactCircIntegrable Q
          (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1),
          ENNReal.ofReal ((3 : ℝ)^(-((Q.scale : ℝ) / 8))) *
            paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ))
              (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1) hf ≤
            ENNReal.ofReal zeta) →
        ∀ e v : H10Function (openCubeSet Q),
          IsMassiveWeakSolutionOn
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) 0
            (openCubeSet Q) e.toH1Function (fun _ => 1) →
          (∀ w : H10Function (openCubeSet Q),
            IsMassiveWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
              (fun _ => 1) 0 (openCubeSet Q) w.toH1Function (fun _ => 1) →
            cubeLpNorm Q 2 (w - v).toH1Function.toFun ≤
              (eps / 2) * (cubeScaleFactor Q)^2 / ahom M L) →
          cubeLpNorm Q 2 (e - v).toH1Function.toFun ≤
            eps * (cubeScaleFactor Q)^2 / ahom M L := by
  set K : ℝ := 32 * (3 : ℝ)^((d : ℝ) + 1 / 2) *
    (weightedLocalSobolevEnergyConstant d)^2 * (1 - (3 : ℝ)^(-(3 / 8 : ℝ)))⁻¹ with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    have h3pos : 0 < (3 : ℝ)^((d : ℝ) + 1 / 2) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
    have hlt : (3 : ℝ)^(-(3 / 8 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
        (by norm_num : -(3 / 8 : ℝ) < 0)
    have hinv : 0 ≤ (1 - (3 : ℝ)^(-(3 / 8 : ℝ)))⁻¹ :=
      inv_nonneg.2 (by linarith)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) h3pos.le)
      (sq_nonneg _)) hinv
  set zeta : ℝ := eps / (18 * (K + 1)) with hzdef
  have hzeta : 0 < zeta := by
    rw [hzdef]
    exact div_pos heps (mul_pos (by norm_num : (0 : ℝ) < 18) (by linarith))
  refine ⟨zeta, hzeta, ?_⟩
  intro M L omega Q hprice hbesovP e v he hcompare
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  obtain ⟨lam, Lam, hlam0, hEllAll⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_isEllipticFieldOn_aCutoff_descendants
      (j := 0) M L omega Q
  have hEll : IsEllipticFieldOn lam Lam (openCubeSet Q)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) :=
    hEllAll Q (by simp)
  let data := aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)
  have hbound : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
      data.lam ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ∧
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ≤ data.Lam := by
    simpa only [Homogenization.volumeMeasureOn,
      Homogenization.Book.Ch02.cubeDomain_coe] using data.aeBounds
  have hnorm : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
      ‖SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x‖ ≤ data.Lam := by
    filter_upwards [hbound] with x hx
    have h0 : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x :=
      data.lam_pos.le.trans hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hx.2
  have hbmeas : Measurable (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) :=
    (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).measurable
  have hbL2 : MemL2On (openCubeSet Q) (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) :=
    MemLp.of_bound hbmeas.aestronglyMeasurable data.Lam hnorm
  have h1 : MemL2On (openCubeSet Q) (fun _ : Vec d => (1 : ℝ)) := memLp_const _
  have hg : MemLp (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1) 2
      (normalizedCubeMeasure Q) :=
    memL2On_openCubeSet_normalizedCubeMeasure (hbL2.sub h1)
  have hf : ExactCircIntegrable Q
      (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1) :=
    exactCircIntegrable_of_continuous Q
      ((SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).sub continuous_const)
  have hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      ((aCutoffFamily M L omega).coeffOn Q).toCoeffField x =
        scalarMatrix (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) := by
    filter_upwards with x
    rfl
  have hBesov : ENNReal.ofReal ((3 : ℝ)^(-((Q.scale : ℝ) / 8))) *
      paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ))
        (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1) hf ≤
      ENNReal.ofReal zeta := hbesovP hf
  have key : K * zeta * 9 ≤ eps / 2 := by
    rw [hzdef]
    have h18 : 0 < (18 : ℝ) * (K + 1) := mul_pos (by norm_num) (by linarith)
    have h2 : (0 : ℝ) < 2 := by norm_num
    have hEq : K * (eps / (18 * (K + 1))) * 9 = (K * 9 * eps) / (18 * (K + 1)) := by ring
    rw [hEq, div_le_div_iff₀ h18 h2]
    nlinarith [hK, heps.le, mul_nonneg hK heps.le]
  have bound : cubeLpNorm Q 2 (e - v).toH1Function.toFun ≤
      K * zeta * (cubeScaleFactor Q)^2 *
        (Ch02.lambdaSq Q (1 / 2) (.finite 1) (aCutoffFamily M L omega))⁻¹ +
        (eps / 2) * (cubeScaleFactor Q)^2 / ahom M L := by
    rw [hKdef]
    exact goodCube_torsion_l2_comparison_of_paper_test_and_unit_comparison hd Q
      (aCutoffFamily M L omega) (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) hb hEll
      hbL2 h1 hg hf hzeta.le hBesov e v he hcompare
  have hlamInv : (Ch02.lambdaSq Q (1 / 2) (.finite 1) (aCutoffFamily M L omega))⁻¹ ≤
      9 / ahom M L :=
    (le_div_iff₀' (ahom_pos M L)).2 hprice
  have hKz : 0 ≤ K * zeta * (cubeScaleFactor Q)^2 :=
    mul_nonneg (mul_nonneg hK hzeta.le) (sq_nonneg _)
  have step1 : K * zeta * (cubeScaleFactor Q)^2 *
      (Ch02.lambdaSq Q (1 / 2) (.finite 1) (aCutoffFamily M L omega))⁻¹ ≤
      (eps / 2) * (cubeScaleFactor Q)^2 / ahom M L := by
    calc K * zeta * (cubeScaleFactor Q)^2 *
          (Ch02.lambdaSq Q (1 / 2) (.finite 1) (aCutoffFamily M L omega))⁻¹ ≤
        K * zeta * (cubeScaleFactor Q)^2 * (9 / ahom M L) :=
          mul_le_mul_of_nonneg_left hlamInv hKz
      _ = (K * zeta * 9) * (cubeScaleFactor Q)^2 / ahom M L := by ring
      _ ≤ (eps / 2) * (cubeScaleFactor Q)^2 / ahom M L :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right key (sq_nonneg _))
            (ahom_pos M L).le
  calc cubeLpNorm Q 2 (e - v).toH1Function.toFun ≤
      K * zeta * (cubeScaleFactor Q)^2 *
        (Ch02.lambdaSq Q (1 / 2) (.finite 1) (aCutoffFamily M L omega))⁻¹ +
        (eps / 2) * (cubeScaleFactor Q)^2 / ahom M L := bound
    _ ≤ (eps / 2) * (cubeScaleFactor Q)^2 / ahom M L +
        (eps / 2) * (cubeScaleFactor Q)^2 / ahom M L :=
        add_le_add step1 (le_refl _)
    _ = eps * (cubeScaleFactor Q)^2 / ahom M L := by ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
