module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionPositiveTailMeasure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionPositiveTailForcing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionPhysicalComparison
@[expose] public section

/-!

An ambient measurable event carries the actual weighted-forcing versus constant-forcing torsion comparison on every fixed translated positive-scale cube. The disorder threshold is chosen before the model, cutoff, scale and translation.
-/

set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Section9
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- An ambient tail for the actual weighted-torsion comparison, with no residual moment or response tests. -/
theorem exists_goodCube_positiveScale_weightedTorsion_ambient_tail
    (d J : ℕ) [NeZero d] (hd : 2 ≤ d) (eps : ℝ) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ c →
      ∀ n m : ℕ, m ≤ n → n - m ≤ J → ∀ z : Vec d,
        ∃ Bad : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d),
          MeasurableSet Bad ∧
          M.P.toMeasure Bad ≤ ENNReal.ofReal
            (Real.exp (-(c ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2)))) ∧
          ∀ omega, omega ∉ Bad →
          ∀ e v : H10Function (openCubeSet (originCube d (m : ℤ))),
            IsMassiveWeakSolutionOn
              (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega))
              (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega)) 0
              (openCubeSet (originCube d (m : ℤ))) e.toH1Function (fun _ => 1) →
            IsMassiveWeakSolutionOn (fun _ => ahom M n) (fun _ => 1) 0
              (openCubeSet (originCube d (m : ℤ))) v.toH1Function (fun _ => 1) →
            cubeLpNorm (originCube d (m : ℤ)) 2
                (fun x => e.toH1Function.toFun x - v.toH1Function.toFun x) ≤
              eps * (cubeScaleFactor (originCube d (m : ℤ))) ^ 2 / ahom M n := by
  have heps2 : 0 < eps / 2 := by linarith
  obtain ⟨zeta, hzeta, hz⟩ :=
    exists_goodCube_cutoff_torsion_comparison_tolerance d hd eps heps
  obtain ⟨cP, eP, hcP, heP, hphys⟩ :=
    exists_goodCube_positiveScale_torsion_comparison d J hd (eps / 2) heps2
  have heObs_pos : 0 < min eP 1 := lt_min heP (by norm_num)
  have heObs_leP : min eP 1 ≤ eP := min_le_left _ _
  have heObs_le1 : min eP 1 ≤ 1 := min_le_right _ _
  obtain ⟨cT, hcT, _, htail⟩ :=
    exists_goodCube_positiveScale_ambient_tail d J hd zeta (min eP 1) hzeta heObs_pos
  obtain ⟨c, hc, hcmin, hc2, habsorb⟩ :=
    goodCube_exists_finite_tail_absorption (1 : ℝ) (cT ^ 2) (min cT cP)
      (by norm_num) (by positivity) (lt_min hcT hcP)
  refine ⟨c, hc, hc2, ?_⟩
  intro M hM n m hmn hnm z
  obtain ⟨Bad, hBadmeas, hBadmeas', hBad⟩ :=
    htail M (le_trans hM (le_trans hcmin (min_le_left cT cP))) n m hmn hnm z
  obtain ⟨B, hBmeas, hBle, hB⟩ :=
    goodCube_exists_measurable_bad_union_null M.P.toMeasure Bad hBadmeas _
      (hphys M (le_trans hM (le_trans hcmin (min_le_right cT cP))) n m hmn hnm z)
  refine ⟨B, hBmeas, ?_, ?_⟩
  · have habs : Real.exp (-(cT ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))) ≤
        Real.exp (-(c ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))) := by
      simpa only [one_mul, neg_div] using
        habsorb M.delta M.shellPrefix.delta_pos hM
    calc M.P.toMeasure B ≤ M.P.toMeasure Bad := hBle
      _ ≤ ENNReal.ofReal
            (Real.exp (-(cT ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) := hBadmeas'
      _ ≤ ENNReal.ofReal
            (Real.exp (-(c ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) :=
            ENNReal.ofReal_le_ofReal habs
  · intro omega homega e v he hv
    obtain ⟨homegaBad, hP⟩ := hB omega homega
    obtain ⟨hE, hprice, hrest⟩ := hBad omega homegaBad
    have hE' : ellipticityMomentObservable M n (m : ℤ) (1 / 8)
        (translatePotentialSample z omega) ≤ ENNReal.ofReal eP :=
      hE.trans (ENNReal.ofReal_le_ofReal heObs_leP)
    have hP' := hP hE'
    have hsqrt2 : Real.sqrt 2 ≤ 2 := by
      have h : Real.sqrt 2 ≤ Real.sqrt (2 ^ 2) :=
        Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 2 ^ 2)
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
      exact h
    have hx : (1 : ℝ) + Real.sqrt 2 * min eP 1 ≤ 3 := by
      have hm : Real.sqrt 2 * min eP 1 ≤ 2 * min eP 1 :=
        mul_le_mul_of_nonneg_right hsqrt2 (le_of_lt heObs_pos)
      linarith
    have hx0 : 0 ≤ (1 : ℝ) + Real.sqrt 2 * min eP 1 := by
      have h := mul_nonneg (Real.sqrt_nonneg 2) (le_of_lt heObs_pos)
      linarith
    have h9 : ((1 : ℝ) + Real.sqrt 2 * min eP 1) ^ 2 ≤ 9 := by
      nlinarith [hx, hx0]
    have hprice9 : ahom M n * (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ ≤ 9 :=
      le_trans hprice h9
    have hconj :
        (((1 / 2 : ℝ) ≤ cubeAverage (originCube d (m : ℤ))
              (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega)) ∧
            cubeAverage (originCube d (m : ℤ))
              (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega)) ≤
              3 / 2) ∧
          (∀ hf : ExactCircIntegrable (originCube d (m : ℤ))
              (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x - 1),
            ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
              paperNegativeBesovCircDiagonal (originCube d (m : ℤ)) (1 / 8) (4 * (d : ℝ))
                (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x - 1) hf ≤
              ENNReal.ofReal zeta) ∧
          (∀ hb : ExactCircIntegrable (originCube d (m : ℤ))
              (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x /
                  cubeAverage (originCube d (m : ℤ))
                    (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega)) - 1),
            ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
              paperNegativeBesovCircDiagonal (originCube d (m : ℤ)) (1 / 8) (4 * (d : ℝ))
                (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x /
                    cubeAverage (originCube d (m : ℤ))
                      (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega)) - 1) hb ≤
              1)) := hrest
    obtain ⟨_, hraw, _⟩ := hconj
    have hscale : (originCube d (m : ℤ)).scale = (m : ℤ) := rfl
    have hexpeq : (-(((m : ℤ) : ℝ) / 8) : ℝ) = -(1 / 8 : ℝ) * (m : ℝ) := by
      push_cast
      ring
    have hrawBesov : ∀ hf : ExactCircIntegrable (originCube d (m : ℤ))
        (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x - 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-(((originCube d (m : ℤ)).scale : ℝ) / 8))) *
          paperNegativeBesovCircDiagonal (originCube d (m : ℤ)) (1 / 8) (4 * (d : ℝ))
            (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x - 1) hf ≤
          ENNReal.ofReal zeta := by
      intro hf
      rw [hscale, hexpeq]
      exact hraw hf
    have hsubEV : (e - v).toH1Function.toFun =
        fun x => e.toH1Function.toFun x - v.toH1Function.toFun x := by
      funext x
      change e.toH1Function.toFun x + (-1) * v.toH1Function.toFun x = _
      ring
    have hunit : ∀ w : H10Function (openCubeSet (originCube d (m : ℤ))),
        IsMassiveWeakSolutionOn
          (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega))
          (fun _ => 1) 0 (openCubeSet (originCube d (m : ℤ))) w.toH1Function (fun _ => 1) →
        cubeLpNorm (originCube d (m : ℤ)) 2 (w - v).toH1Function.toFun ≤
          (eps / 2) * (cubeScaleFactor (originCube d (m : ℤ))) ^ 2 / ahom M n := by
      intro w hw
      have hsubWV : (w - v).toH1Function.toFun =
          fun x => w.toH1Function.toFun x - v.toH1Function.toFun x := by
        funext x
        change w.toH1Function.toFun x + (-1) * v.toH1Function.toFun x = _
        ring
      rw [hsubWV]
      exact hP' w v hw hv
    have hfin := hz M n (translatePotentialSample z omega) (originCube d (m : ℤ)) hprice9
      hrawBesov e v he hunit
    rw [hsubEV] at hfin
    exact hfin

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
