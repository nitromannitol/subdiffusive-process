import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.CoarseGrainingVocab.Core
import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationErrorDefault
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_iteration

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

attribute [local instance] Classical.propDecidable

theorem aux_lem_repair_err_fold_carrier_bridge_fold_affine
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P : Finset (Fin d)) (x : SpatialCoordinates d) :
    coordinateFold z I P (fun i => z i + r * x i) =
      (fun i => z i + r * coordinateFold 0 I P x i) := by
  funext i
  by_cases hi : i ∈ I
  · simp [coordinateFold, coordinateReflectionSign, hi, abs_mul, abs_of_pos hr]
  · simp [coordinateFold, hi]

theorem aux_lem_repair_err_fold_carrier_bridge_fold_qmp
    {d : ℕ} (z : SpatialCoordinates d) (I P : Finset (Fin d)) :
    Measure.QuasiMeasurePreserving (coordinateFold z I P) volume volume := by
  classical
  refine ⟨(coordinateFold_continuous z I P).measurable, ?_⟩
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  rw [Measure.map_apply (coordinateFold_continuous z I P).measurable hs]
  refine measure_mono_null
      (s := coordinateFold z I P ⁻¹' s)
      (t := ⋃ J : Finset (Fin d), coordinateReflection z J ⁻¹' s) ?_ ?_
  · intro x hx
    let J : Finset (Fin d) :=
      I.filter (fun i => if i ∈ P then z i ≤ x i else x i < z i)
    have hfold : coordinateFold z I P x = coordinateReflection z J x := by
      funext i
      by_cases hi : i ∈ I
      · by_cases hp : i ∈ P
        · by_cases hxi : z i ≤ x i
          · have hJi : i ∈ J := by simp [J, hi, hp, hxi]
            simp only [coordinateFold, hi, if_pos, coordinateReflection, hJi,
              coordinateReflectionSign, hp, if_pos]
            rw [abs_of_nonneg (sub_nonneg.mpr hxi)]
            ring
          · have hJi : i ∉ J := by simp [J, hi, hp, hxi]
            have hxz : x i ≤ z i := le_of_not_ge hxi
            simp only [coordinateFold, hi, if_pos, coordinateReflection, hJi,
              if_false, coordinateReflectionSign, hp, if_pos]
            rw [abs_of_nonpos (sub_nonpos.mpr hxz)]
            ring
        · by_cases hxi : z i ≤ x i
          · have hJi : i ∉ J := by simp [J, hi, hp, hxi]
            simp only [coordinateFold, hi, if_pos, coordinateReflection, hJi,
              if_false, coordinateReflectionSign, hp, if_false]
            rw [abs_of_nonneg (sub_nonneg.mpr hxi)]
            ring
          · have hxz : x i < z i := lt_of_not_ge hxi
            have hJi : i ∈ J := by simp [J, hi, hp, hxz]
            simp only [coordinateFold, hi, if_pos, coordinateReflection, hJi,
              if_pos, coordinateReflectionSign, hp, if_false]
            rw [abs_of_nonpos (sub_nonpos.mpr hxz.le)]
            ring
      · have hJi : i ∉ J := by simp [J, hi]
        simp [coordinateFold, coordinateReflection, hi, hJi]
    exact Set.mem_iUnion_of_mem J (by simpa [hfold] using hx)
  · apply measure_iUnion_null
    intro J
    exact
      (coordinateReflection_measurePreserving z J).quasiMeasurePreserving.preimage_null
        hzero

theorem aux_lem_repair_err_fold_carrier_bridge_affine_maps_root
    {d : ℕ} (z : SpatialCoordinates d) (r R : ℝ) (hr : 0 < r)
    (hR : 0 < R) (hrR : r ≤ R) (Q : Homogenization.TriadicCube d)
    (hQ : Homogenization.openCubeSet Q ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    Set.MapsTo (fun x : SpatialCoordinates d => z + r • x)
      (Homogenization.openCubeSet Q)
      (centeredCube z R hR : Set (SpatialCoordinates d)) := by
  intro x hx
  have hunit :
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) =
        Homogenization.openCubeSet (Homogenization.originCube d 0) := by
    simpa using
      (SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube (d := d) 0
        (by norm_num : (0 : ℝ) < (3 : ℝ) ^ (0 : ℤ)))
  have hxunit : x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos := by
    change x ∈ (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))
    rw [hunit]
    exact hQ hx
  have hxnorm : dist x (0 : SpatialCoordinates d) < (1 : ℝ) / 2 := by
    exact hxunit
  have hdist : dist (z + r • x) z = r * dist x 0 := by
    rw [dist_eq_norm, dist_eq_norm]
    simp [norm_smul, abs_of_pos hr]
  change dist (z + r • x) z < R / 2
  rw [hdist]
  calc
    r * dist x 0 ≤ R * dist x 0 :=
      mul_le_mul_of_nonneg_right hrR (dist_nonneg)
    _ < R * ((1 : ℝ) / 2) := mul_lt_mul_of_pos_left hxnorm hR
    _ = R / 2 := by ring

theorem aux_lem_repair_err_fold_carrier_bridge_paper_probe_aeeq
    {d : ℕ} {A B : Homogenization.Book.Ch02.TriadicCoeffFamily d}
    {Q : Homogenization.TriadicCube d}
    (h : Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn Q) (B.coeffOn Q))
    (alpha : ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q A alpha =
      SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q B alpha := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe
    SubdiffusiveProcess.CoarseGrainingVocab.J
  apply iSup_congr
  intro e
  congr 1
  exact Homogenization.Book.Ch02.responseJ_eq_ofAEEq h _ _

theorem aux_lem_repair_err_fold_carrier_bridge_paper_error_aeeq
    {d : ℕ} (Q₀ : Homogenization.TriadicCube d)
    (s alpha : ℝ)
    (A B : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (h : ∀ (k : ℤ) (Q : Homogenization.TriadicCube d),
      Q ∈ Homogenization.descendantsAtScale Q₀ k →
        Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn Q) (B.coeffOn Q)) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError Q₀ 0 s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) A alpha =
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError Q₀ 0 s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) B alpha := by
  rw [SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError_infinity_two_eq_weighted_series,
    SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError_infinity_two_eq_weighted_series]
  congr 1
  apply tsum_congr
  intro l
  have hscale :
      SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale Q₀ (0 - (l : ℤ)) A alpha =
        SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale Q₀ (0 - (l : ℤ)) B alpha := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
    apply iSup_congr
    intro R
    exact aux_lem_repair_err_fold_carrier_bridge_paper_probe_aeeq
      (h (0 - (l : ℤ)) R.1 R.2) alpha
  rw [hscale]



theorem lem_repair_err_fold_carrier_bridge :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
    ∀ (L m : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
      (om : BilateralField d) (I P : Finset (Fin d)),
      I.Nonempty →
      ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
        ((foldedCoef.val : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
          fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val
            (coordinateFold z I P x)) →
        ∀ j : ℕ, j + 2 ≤ L → j + 2 ≤ m →
          ∃ a : SpatialCoordinates d → ℝ,
            Continuous a ∧ (∀ x, 0 < a x) ∧
            ∃ origData : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData a,
              ∃ foldData : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData
                  (fun x => a (coordinateFold 0 I P x)),
                E.err z ((3 : ℝ) ^ m) hR foldedCoef z ((3 : ℝ) ^ (j + 2))
                    (It.ref L j z om) It.s0 2 =
                    (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError
                      (Homogenization.originCube d 0) 0 It.s0
                      Homogenization.Book.Ch02.MultiscaleExponent.infinity
                      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
                      foldData.toTriadicCoeffFamily (It.ref L j z om)).toReal ∧
                E.err z ((3 : ℝ) ^ m) hR
                    (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z
                    ((3 : ℝ) ^ (j + 2)) (It.ref L j z om) It.s0 2 =
                    (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError
                      (Homogenization.originCube d 0) 0 It.s0
                      Homogenization.Book.Ch02.MultiscaleExponent.infinity
                      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
                      origData.toTriadicCoeffFamily (It.ref L j z om)).toReal := by
  intro d _ _ _ E M Sreg It L m z hR om I P hI foldedCoef hfolded j hjL hjm
  letI : NeZero d := ⟨by omega⟩
  let r : ℝ := (3 : ℝ) ^ (j + 2)
  let R : ℝ := (3 : ℝ) ^ m
  let f : SpatialCoordinates d → SpatialCoordinates d :=
    fun x i => z i + r * x i
  let a : SpatialCoordinates d → ℝ :=
    fun x => Real.exp
      ((∑ k ∈ Finset.range (L + 1), (om (k : ℤ)) (f x)) -
        (L + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hR' : 0 < R := by
    change 0 < (3 : ℝ) ^ m
    exact hR
  have hrr : r ≤ R := by
    dsimp [r, R]
    exact pow_le_pow_right₀ (by norm_num) hjm
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    dsimp [f]
    exact continuous_const.add (continuous_const.mul (continuous_apply i))
  have ha : Continuous a := by
    dsimp [a]
    exact Real.continuous_exp.comp
      (Continuous.sub
        (continuous_finset_sum _ fun k _ => (om (k : ℤ)).continuous.comp hf)
        continuous_const)
  have ha_pos : ∀ x, 0 < a x := by
    intro x
    dsimp [a]
    exact Real.exp_pos _
  have hfa : ∀ x, coordinateFold z I P (f x) = f (coordinateFold 0 I P x) := by
    intro x
    simpa [f, Pi.smul_apply, smul_eq_mul] using
      aux_lem_repair_err_fold_carrier_bridge_fold_affine z r hr I P x
  let origData : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData a :=
    { onCube := fun Q => Classical.choice
        (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
          ha ha_pos (Homogenization.Book.Ch02.cubeDomain Q)) }
  have hfa_cont : Continuous (fun x => a (coordinateFold 0 I P x)) :=
    ha.comp (coordinateFold_continuous 0 I P)
  have hfa_pos : ∀ x, 0 < a (coordinateFold 0 I P x) :=
    fun x => ha_pos _
  let foldData : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData
      (fun x => a (coordinateFold 0 I P x)) :=
    { onCube := fun Q => Classical.choice
        (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
          hfa_cont hfa_pos (Homogenization.Book.Ch02.cubeDomain Q)) }
  have hf_qmp : Measure.QuasiMeasurePreserving f volume volume := by
    have h :=
      (MeasureTheory.measurePreserving_add_left volume z).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_smul volume (ne_of_gt hr))
    simpa [f, Function.comp_def, Pi.smul_apply, smul_eq_mul] using h
  have hfold_qmp :=
    aux_lem_repair_err_fold_carrier_bridge_fold_qmp z I P
  have hinner : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z R hR' : Set (SpatialCoordinates d)) := by
    change Metric.ball z (r / 2) ⊆ Metric.ball z (R / 2)
    exact Metric.ball_subset_ball (by linarith)
  have hmaps (Q : Homogenization.TriadicCube d)
      (hQ : Homogenization.openCubeSet Q ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0)) :
      Set.MapsTo f (Homogenization.openCubeSet Q)
        (centeredCube z R hR' : Set (SpatialCoordinates d)) := by
    intro x hx
    simpa [f, Pi.smul_apply, smul_eq_mul] using
      aux_lem_repair_err_fold_carrier_bridge_affine_maps_root z r R hr hR' hrr Q hQ hx
  have hmaps_fold (Q : Homogenization.TriadicCube d)
      (hQ : Homogenization.openCubeSet Q ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0)) :
      Set.MapsTo (coordinateFold z I P ∘ f)
        (Homogenization.openCubeSet Q)
        (centeredCube z R hR' : Set (SpatialCoordinates d)) := by
    intro x hx
    have hxf := hmaps Q hQ hx
    have hxf' : coordinateFold z I P (f x) ∈
        (centeredCube z R hR' : Set (SpatialCoordinates d)) := by
      change dist (coordinateFold z I P (f x)) z < R / 2
      rw [coordinateFold_dist_center]
      change dist (f x) z < R / 2 at hxf
      exact hxf
    exact hxf'
  have hcut := Sreg.cutoffOn_eq L om z ((3 : ℝ) ^ m) hR
  have horig_ae (Q : Homogenization.TriadicCube d)
      (hQ : Homogenization.openCubeSet Q ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0)) :
      (fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (f x)) =ᵐ[
        volume.restrict (Homogenization.openCubeSet Q)] fun x => a x := by
    have h :=
      (hf_qmp.restrict (hmaps Q hQ)).ae_eq_comp hcut
    simpa [a, f, Function.comp_def, Pi.smul_apply, smul_eq_mul] using h
  have hfold_ae (Q : Homogenization.TriadicCube d)
      (hQ : Homogenization.openCubeSet Q ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0)) :
      (fun x => foldedCoef.val (f x)) =ᵐ[
        volume.restrict (Homogenization.openCubeSet Q)]
        fun x => a (coordinateFold 0 I P x) := by
    have h₁ :=
      (hf_qmp.restrict (hmaps Q hQ)).ae_eq_comp hfolded
    have h₂ :=
      ((hfold_qmp.comp hf_qmp).restrict (hmaps_fold Q hQ)).ae_eq_comp hcut
    have h₁' : (fun x => foldedCoef.val (f x)) =ᵐ[
        volume.restrict (Homogenization.openCubeSet Q)]
        (fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val
          (coordinateFold z I P (f x))) := by
      simpa [Function.comp_def] using h₁
    have h₂' : (fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val
          (coordinateFold z I P (f x))) =ᵐ[
        volume.restrict (Homogenization.openCubeSet Q)]
        (fun x => Real.exp
          ((∑ k ∈ Finset.range (L + 1), (om (k : ℤ))
              (coordinateFold z I P (f x))) -
            (L + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
      simpa [Function.comp_def] using h₂
    filter_upwards [h₁', h₂'] with x hx₁ hx₂
    calc
      foldedCoef.val (f x) =
          (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val
            (coordinateFold z I P (f x)) := hx₁
      _ = Real.exp
          ((∑ k ∈ Finset.range (L + 1), (om (k : ℤ))
              (coordinateFold z I P (f x))) -
            (L + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := hx₂
      _ = a (coordinateFold 0 I P x) := by
        rw [hfa x]
  have horig_chart (Q : Homogenization.TriadicCube d)
      (hQ : Homogenization.openCubeSet Q ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0)) :
      Homogenization.Book.Ch02.CoeffOn.AEEq
        ((E.chart z ((3 : ℝ) ^ m) hR
          (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z r).coeffOn Q)
        (origData.toTriadicCoeffFamily.coeffOn Q) := by
    unfold Homogenization.Book.Ch02.CoeffOn.AEEq
    change ((E.chart z ((3 : ℝ) ^ m) hR
          (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z r).coeffOn Q).toCoeffField =ᵐ[
        volume.restrict (Homogenization.openCubeSet Q)]
      (fun x => Homogenization.scalarMatrix (a x))
    have hc := E.chart_eq z ((3 : ℝ) ^ m) hR
      (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z r hr hinner Q hQ
    have haee := horig_ae Q hQ
    filter_upwards [hc, haee] with x hcx hax
    calc
      ((E.chart z ((3 : ℝ) ^ m) hR
          (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z r).coeffOn Q).toCoeffField x =
          Homogenization.scalarMatrix
            ((Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (f x)) := by
        simpa [f, Pi.smul_apply, smul_eq_mul] using hcx
      _ = Homogenization.scalarMatrix (a x) := by rw [hax]
  have hfold_chart (Q : Homogenization.TriadicCube d)
      (hQ : Homogenization.openCubeSet Q ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0)) :
      Homogenization.Book.Ch02.CoeffOn.AEEq
        ((E.chart z ((3 : ℝ) ^ m) hR foldedCoef z r).coeffOn Q)
        (foldData.toTriadicCoeffFamily.coeffOn Q) := by
    unfold Homogenization.Book.Ch02.CoeffOn.AEEq
    change ((E.chart z ((3 : ℝ) ^ m) hR foldedCoef z r).coeffOn Q).toCoeffField =ᵐ[
        volume.restrict (Homogenization.openCubeSet Q)]
      (fun x => Homogenization.scalarMatrix (a (coordinateFold 0 I P x)))
    have hc := E.chart_eq z ((3 : ℝ) ^ m) hR foldedCoef z r hr hinner Q hQ
    have haee := hfold_ae Q hQ
    filter_upwards [hc, haee] with x hcx hax
    calc
      ((E.chart z ((3 : ℝ) ^ m) hR foldedCoef z r).coeffOn Q).toCoeffField x =
          Homogenization.scalarMatrix (foldedCoef.val (f x)) := by
        simpa [f, Pi.smul_apply, smul_eq_mul] using hcx
      _ = Homogenization.scalarMatrix (a (coordinateFold 0 I P x)) := by rw [hax]
  have horig_local (k : ℤ) (Q : Homogenization.TriadicCube d)
      (hQ : Q ∈ Homogenization.descendantsAtScale
        (Homogenization.originCube d 0) k) :
      Homogenization.Book.Ch02.CoeffOn.AEEq
        ((E.chart z ((3 : ℝ) ^ m) hR
          (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z r).coeffOn Q)
        (origData.toTriadicCoeffFamily.coeffOn Q) :=
    horig_chart Q (Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
      (Homogenization.descendant_scale_le_of_mem_descendantsAtScale hQ) hQ)
  have hfold_local (k : ℤ) (Q : Homogenization.TriadicCube d)
      (hQ : Q ∈ Homogenization.descendantsAtScale
        (Homogenization.originCube d 0) k) :
      Homogenization.Book.Ch02.CoeffOn.AEEq
        ((E.chart z ((3 : ℝ) ^ m) hR foldedCoef z r).coeffOn Q)
        (foldData.toTriadicCoeffFamily.coeffOn Q) :=
    hfold_chart Q (Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
      (Homogenization.descendant_scale_le_of_mem_descendantsAtScale hQ) hQ)
  have hpaper_orig :=
    aux_lem_repair_err_fold_carrier_bridge_paper_error_aeeq
      (Homogenization.originCube d 0) It.s0 (It.ref L j z om)
      (E.chart z ((3 : ℝ) ^ m) hR
        (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z r)
      origData.toTriadicCoeffFamily horig_local
  have hpaper_fold :=
    aux_lem_repair_err_fold_carrier_bridge_paper_error_aeeq
      (Homogenization.originCube d 0) It.s0 (It.ref L j z om)
      (E.chart z ((3 : ℝ) ^ m) hR foldedCoef z r)
      foldData.toTriadicCoeffFamily hfold_local
  have hs : It.s0 ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [It.s0_eq]
    norm_num
  have href : 0 < It.ref L j z om := It.ref_pos L j z om
  have herr_orig := E.err_eq z ((3 : ℝ) ^ m) hR
    (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z r hr hinner
    It.s0 hs (2 : ℝ≥0∞) (by norm_num) (It.ref L j z om) href
  have herr_fold := E.err_eq z ((3 : ℝ) ^ m) hR foldedCoef z r hr hinner
    It.s0 hs (2 : ℝ≥0∞) (by norm_num) (It.ref L j z om) href
  refine ⟨a, ha, ha_pos, origData, foldData, ?_, ?_⟩
  · calc
      E.err z ((3 : ℝ) ^ m) hR foldedCoef z r (It.ref L j z om) It.s0 2 =
          (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError
            (Homogenization.originCube d 0) 0 It.s0
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
            (E.chart z ((3 : ℝ) ^ m) hR foldedCoef z r)
            (It.ref L j z om)).toReal := by
        simpa using herr_fold
      _ = (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError
            (Homogenization.originCube d 0) 0 It.s0
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
            foldData.toTriadicCoeffFamily (It.ref L j z om)).toReal := by
        rw [hpaper_fold]
  · calc
      E.err z ((3 : ℝ) ^ m) hR
          (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z r
          (It.ref L j z om) It.s0 2 =
          (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError
            (Homogenization.originCube d 0) 0 It.s0
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
            (E.chart z ((3 : ℝ) ^ m) hR
              (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z r)
            (It.ref L j z om)).toReal := by
        simpa using herr_orig
      _ = (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError
            (Homogenization.originCube d 0) 0 It.s0
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
            origData.toTriadicCoeffFamily (It.ref L j z om)).toReal := by
        rw [hpaper_orig]

end Paper
