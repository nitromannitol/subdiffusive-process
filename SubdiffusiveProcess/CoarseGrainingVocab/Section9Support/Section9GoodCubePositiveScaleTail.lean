module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePositiveScaleTailParameters

@[expose] public section

/-!
# Ambient positive-scale good-cube tail for one translated descendant

A common choice of small-disorder exponent pays a parent Besov test and an
arbitrarily small actual descendant response test. The response majorant
ranges over all higher cutoffs. This file therefore asserts ambient
measurability, leaving restricted-coefficient locality to a separate step.
-/

set_option autoImplicit false
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Section9
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
/-- An ambient measurable majorant for one translated descendant cube. The
response observable includes all higher cutoffs; no restricted-coefficient
locality is asserted. Both the raw Besov and response tolerances are arbitrary. -/
theorem exists_goodCube_positiveScale_ambient_tail
    (d J : ℕ) [NeZero d] (hd : 2 ≤ d) (zeta e : ℝ) (hzeta : 0 < zeta) (he : 0 < e) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ c →
      ∀ n m : ℕ, m ≤ n → n - m ≤ J → ∀ z : Vec d,
        ∃ Bad : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d),
          MeasurableSet Bad ∧
          M.P.toMeasure Bad ≤ ENNReal.ofReal
            (Real.exp (-(c^2 / (M.delta^2 * Real.log M.delta^2)))) ∧
          ∀ omega, omega ∉ Bad →
            ellipticityMomentObservable M n (m : ℤ) (1 / 8)
              (translatePotentialSample z omega) ≤ ENNReal.ofReal e ∧
            ahom M n * (Homogenization.Book.Ch02.lambdaSq (originCube d (m : ℤ))
              (1 / 2) (.finite 1) (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ ≤
                (1 + Real.sqrt 2 * e)^2 ∧
            let Q := originCube d (m : ℤ)
            let a := _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega)
            ((1 / 2 : ℝ) ≤ cubeAverage Q a ∧ cubeAverage Q a ≤ 3 / 2) ∧
            (∀ hf : ExactCircIntegrable Q (fun x => a x - 1),
              ENNReal.ofReal ((3 : ℝ)^(-(1 / 8 : ℝ) * (m : ℝ))) *
                paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ)) (fun x => a x - 1) hf ≤
                  ENNReal.ofReal zeta) ∧
            (∀ hb : ExactCircIntegrable Q (fun x => a x / cubeAverage Q a - 1),
              ENNReal.ofReal ((3 : ℝ)^(-(1 / 8 : ℝ) * (m : ℝ))) *
                paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ))
                  (fun x => a x / cubeAverage Q a - 1) hb ≤ 1) := by
  let G : ℝ := (3 : ℝ)^((J : ℝ) / 8)
  have hG : 0 < G := Real.rpow_pos_of_pos (by norm_num) _
  let beta : ℝ := min (zeta / (4 * G)) ((32 * G)⁻¹)
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hbetaZ : 4 * G * beta ≤ zeta := by
    have h := (le_div_iff₀ (show 0 < 4 * G by positivity)).mp
      (show beta ≤ zeta / (4 * G) from min_le_left _ _)
    nlinarith only [h]
  have hbetaMass : beta ≤ (32 * G)⁻¹ := min_le_right _ _
  obtain ⟨a, delta0, ha, hdelta0, hparams⟩ :=
    exists_goodCube_positiveScale_moment_parameters d J e beta he hbeta
  obtain ⟨c, hc, hcdelta, hchalf, habsorb⟩ :=
    goodCube_exists_finite_tail_absorption 2 (a * Real.log 4) delta0
      (by norm_num) (by positivity) hdelta0
  refine ⟨c, hc, hchalf, ?_⟩
  intro M hM n m hmn hmJ z
  let p : ℝ := smallDisorderExponent a M.delta
  obtain ⟨hp2, hp32, hmoments⟩ := hparams M (hM.trans hcdelta)
  have hp0 : 0 < p := by change 0 < smallDisorderExponent a M.delta; linarith
  obtain ⟨hZmom, hEmom⟩ := hmoments n m hmn hmJ z
  let Z := goodCubeParentBesovObservable M n p z
  let E := fun omega => ellipticityMomentObservable M n (m : ℤ) (1 / 8)
    (translatePotentialSample z omega)
  have hZmeas : Measurable Z := measurable_goodCubeParentBesovObservable M n p z
  have hEmeas : Measurable E :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.measurable_ellipticityMomentObservable M n (m : ℤ) (1 / 8)).comp
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.measurable_translatePotentialSample z)
  have hZtail := goodCube_markov_quarter_tail M.P.toMeasure p beta hp0 hbeta Z hZmeas hZmom
  have hEtail := goodCube_markov_quarter_tail M.P.toMeasure p e hp0 he E hEmeas hEmom
  let Bad := {omega | ENNReal.ofReal beta < Z omega} ∪ {omega | ENNReal.ofReal e < E omega}
  have hBadMeas : MeasurableSet Bad := hZtail.1.union hEtail.1
  have hBadTail : M.P.toMeasure Bad ≤ ENNReal.ofReal (2 * Real.exp (-p * Real.log 4)) := by
    calc
      _ ≤ M.P.toMeasure {omega | ENNReal.ofReal beta < Z omega} +
          M.P.toMeasure {omega | ENNReal.ofReal e < E omega} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-p * Real.log 4)) +
          ENNReal.ofReal (Real.exp (-p * Real.log 4)) := add_le_add hZtail.2 hEtail.2
      _ = ENNReal.ofReal (2 * Real.exp (-p * Real.log 4)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
  have hlog : Real.log M.delta ≠ 0 := ne_of_lt
    (Real.log_neg M.shellPrefix.delta_pos ((hM.trans hchalf).trans_lt (by norm_num)))
  have hpEq : p = a / (M.delta^2 * Real.log M.delta^2) := by
    dsimp [p]
    rw [smallDisorderExponent_eq_div M.shellPrefix.delta_pos.ne' hlog, sq_abs]
  have hexp : -p * Real.log 4 = -(a * Real.log 4 / (M.delta^2 * Real.log M.delta^2)) := by
    rw [hpEq]
    ring
  rw [hexp] at hBadTail
  refine ⟨Bad, hBadMeas, hBadTail.trans (ENNReal.ofReal_le_ofReal
    (by simpa only [neg_div] using habsorb M.delta M.shellPrefix.delta_pos hM)), ?_⟩
  intro omega homega
  have hnot : ¬ (ENNReal.ofReal beta < Z omega ∨ ENNReal.ofReal e < E omega) := homega
  have hZpoint : Z omega ≤ ENNReal.ofReal beta := le_of_not_gt (fun h => hnot (Or.inl h))
  have hEpoint : E omega ≤ ENNReal.ofReal e := le_of_not_gt (fun h => hnot (Or.inr h))
  refine ⟨hEpoint, goodCube_cutoff_lambda_price_le_of_ellipticity_test M n m hmn z omega he.le hEpoint, ?_⟩
  let coeff := _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega)
  have hf : ExactCircIntegrable (originCube d (n : ℤ)) (fun x => coeff x - 1) :=
    exactCircIntegrable_of_continuous _
      ((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M n (translatePotentialSample z omega)).sub continuous_const)
  have hrawParent : ENNReal.ofReal ((3 : ℝ)^(-(1 / 16 : ℝ) * (n : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d (n : ℤ)) (1 / 16) p (fun x => coeff x - 1) hf ≤
        ENNReal.ofReal beta := by
    rw [← goodCubeParentBesovObservable_eq M n p z omega hf]
    exact hZpoint
  have hpair := goodCube_cutoff_descendant_mass_and_besov_tests hd M n m J hmn hmJ p hp32 z omega hf
    (hrawParent.trans (ENNReal.ofReal_le_ofReal hbetaMass))
  refine ⟨hpair.1, ?_, hpair.2⟩
  intro hfm
  exact (goodCube_descendant_raw_besov_le_of_parent hd n m J hmn hmJ p hp32 beta hbeta.le
    (fun x => coeff x - 1) hf hrawParent hfm).trans (ENNReal.ofReal_le_ofReal hbetaZ)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
