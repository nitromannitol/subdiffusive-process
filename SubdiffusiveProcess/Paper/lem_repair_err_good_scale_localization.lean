import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.CoarseGrainingVocab.Core
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_J

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

attribute [local instance] Classical.propDecidable

theorem aux_lem_repair_err_good_scale_localization_probe
    {d : ℕ} {A B : Homogenization.Book.Ch02.TriadicCoeffFamily d}
    {Q : Homogenization.TriadicCube d}
    (h : Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn Q) (B.coeffOn Q))
    (alpha : ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q A alpha =
      SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q B alpha := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe
  apply iSup_congr
  intro e
  congr 1
  exact Homogenization.Book.Ch02.responseJ_eq_ofAEEq h _ _

theorem aux_lem_repair_err_good_scale_localization_scale
    {d : ℕ} {A B : Homogenization.Book.Ch02.TriadicCoeffFamily d}
    (Q : Homogenization.TriadicCube d) (k : ℤ)
    (h : ∀ R : Homogenization.TriadicCube d,
      R ∈ Homogenization.descendantsAtScale Q k →
        Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn R) (B.coeffOn R))
    (p : Homogenization.Book.Ch02.MultiscaleExponent) (alpha : ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q k p A alpha =
      SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q k p B alpha := by
  cases p with
  | finite p =>
      simp only [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro R _hR
      rw [aux_lem_repair_err_good_scale_localization_probe (h R _hR) alpha]
  | infinity =>
      simp only [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale,
        SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale]
      congr 1
      apply iSup_congr
      intro R
      exact aux_lem_repair_err_good_scale_localization_probe (h R.1 R.2) alpha

theorem aux_lem_repair_err_good_scale_localization_error
    {d : ℕ} {A B : Homogenization.Book.Ch02.TriadicCoeffFamily d}
    (Q : Homogenization.TriadicCube d) (n : ℤ) (s : ℝ)
    (p : Homogenization.Book.Ch02.MultiscaleExponent) (q : ℝ)
    (alpha : ℝ)
    (h : ∀ k : ℤ, ∀ R : Homogenization.TriadicCube d,
      R ∈ Homogenization.descendantsAtScale Q k →
        Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn R) (B.coeffOn R))
    :
    SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite Q n s p q A alpha =
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite Q n s p q B alpha := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
  congr 1
  apply tsum_congr
  intro l
  rw [aux_lem_repair_err_good_scale_localization_scale Q
    (n - (l : ℤ)) (h (n - (l : ℤ))) p alpha]

theorem aux_lem_repair_err_good_scale_localization_error_infinity
    {d : ℕ} {A B : Homogenization.Book.Ch02.TriadicCoeffFamily d}
    (Q : Homogenization.TriadicCube d) (n : ℤ) (s : ℝ)
    (p : Homogenization.Book.Ch02.MultiscaleExponent) (alpha : ℝ)
    (h : ∀ k : ℤ, ∀ R : Homogenization.TriadicCube d,
      R ∈ Homogenization.descendantsAtScale Q k →
        Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn R) (B.coeffOn R))
    :
    SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity Q n s p A alpha =
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity Q n s p B alpha := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity
  apply iSup_congr
  intro l
  congr 1
  exact aux_lem_repair_err_good_scale_localization_scale Q
    (n - (l : ℤ)) (h (n - (l : ℤ))) p alpha

theorem aux_lem_repair_err_good_scale_localization_hunit
    {d : ℕ} :
    (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
        Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet (Homogenization.originCube d 0) := by
  rw [← SubdiffusiveProcess.centeredCube_eq_openCubeSet
    (Homogenization.originCube d 0) (by norm_num)]
  have hc : Homogenization.cubeCenter (Homogenization.originCube d 0) =
      (0 : SpatialCoordinates d) := by
    funext i
    simp [Homogenization.cubeCenter, Homogenization.originCube,
      Homogenization.cubeScaleFactor]
  have hs : Homogenization.cubeScaleFactor (Homogenization.originCube d 0) =
      (1 : ℝ) := by
    simp [Homogenization.originCube, Homogenization.cubeScaleFactor]
  simpa only [hc, hs]



theorem lem_repair_err_good_scale_localization :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Sreg : in_6_16 d M),
    ∀ (L m j : ℕ) (z : SpatialCoordinates d)
      (hR : (0 : ℝ) < 3 ^ m) (hRj : (0 : ℝ) < 3 ^ (j + 2))
      (om : BilateralField d) (a0 s : ℝ) (q : ℝ≥0∞),
      j + 2 ≤ m →
      s ∈ Set.Ioc (0 : ℝ) 1 → 1 ≤ q → 0 < a0 →
      E.err z ((3 : ℝ) ^ m) hR (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR)
          z ((3 : ℝ) ^ (j + 2)) a0 s q =
        E.err z ((3 : ℝ) ^ (j + 2)) hRj
          (Sreg.cutoffOn L om z ((3 : ℝ) ^ (j + 2)) hRj)
          z ((3 : ℝ) ^ (j + 2)) a0 s q := by
  intro d hd instMeas instBorel E M Sreg L m j z hR hRj om a0 s q hjm hs hq ha0
  letI : NeZero d := ⟨by omega⟩
  let aR := Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR
  let ar := Sreg.cutoffOn L om z ((3 : ℝ) ^ (j + 2)) hRj
  have hscale : (3 : ℝ) ^ (j + 2) ≤ (3 : ℝ) ^ m := by
    exact pow_le_pow_right₀ (by norm_num) hjm
  have hsub :
      (centeredCube z ((3 : ℝ) ^ (j + 2)) hRj : Set (SpatialCoordinates d)) ⊆
        (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) := by
    rw [centeredCube_eq_pi z hRj, centeredCube_eq_pi z hR]
    intro x hx i hi
    rcases hx i hi with ⟨hlo, hhi⟩
    constructor <;> linarith
  have hphys : aR.val =ᵐ[volume.restrict
      (centeredCube z ((3 : ℝ) ^ (j + 2)) hRj : Set (SpatialCoordinates d))] ar.val := by
    have hroot := Sreg.cutoffOn_eq L om z ((3 : ℝ) ^ m) hR
    have hroot' := ae_restrict_of_ae_restrict_of_subset hsub hroot
    have hinner := Sreg.cutoffOn_eq L om z ((3 : ℝ) ^ (j + 2)) hRj
    let f : SpatialCoordinates d → ℝ := fun x =>
      Real.exp ((∑ j ∈ Finset.range (L + 1), (om (j : ℤ)) x) -
        (L + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    have hroot'' : aR.val =ᵐ[volume.restrict
        (centeredCube z ((3 : ℝ) ^ (j + 2)) hRj : Set (SpatialCoordinates d))] f := by
      simpa only [aR, f] using hroot'
    have hinner'' : ar.val =ᵐ[volume.restrict
        (centeredCube z ((3 : ℝ) ^ (j + 2)) hRj : Set (SpatialCoordinates d))] f := by
      simpa only [ar, f] using hinner
    exact hroot''.trans hinner''.symm
  have hunit :
      (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d)) =
        Homogenization.openCubeSet (Homogenization.originCube d 0) :=
    aux_lem_repair_err_good_scale_localization_hunit
  have hchart : ∀ (k : ℤ) (Q : Homogenization.TriadicCube d),
      Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) k →
        Homogenization.Book.Ch02.CoeffOn.AEEq
          ((E.chart z ((3 : ℝ) ^ m) hR aR z ((3 : ℝ) ^ (j + 2))).coeffOn Q)
          ((E.chart z ((3 : ℝ) ^ (j + 2)) hRj ar z ((3 : ℝ) ^ (j + 2))).coeffOn Q) := by
    intro k Q hQmem
    have hk : k ≤ (Homogenization.originCube d 0).scale :=
      Homogenization.descendant_scale_le_of_mem_descendantsAtScale hQmem
    have hQ : Homogenization.openCubeSet Q ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0) := by
      exact Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
        (by simpa [Homogenization.originCube] using hk) hQmem
    have hrootQ := E.chart_eq z ((3 : ℝ) ^ m) hR aR z
      ((3 : ℝ) ^ (j + 2)) hRj hsub Q hQ
    have hinnerQ := E.chart_eq z ((3 : ℝ) ^ (j + 2)) hRj ar z
      ((3 : ℝ) ^ (j + 2)) hRj Set.Subset.rfl Q hQ
    let T : SpatialCoordinates d → SpatialCoordinates d :=
      SubdiffusiveProcess.Lane4.cubeDilation z 0 ((3 : ℝ) ^ (j + 2))
    have hqm : Measure.QuasiMeasurePreserving T
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d)))
        (volume.restrict (centeredCube z ((3 : ℝ) ^ (j + 2)) hRj :
          Set (SpatialCoordinates d))) := by
      refine ⟨?_, ?_⟩
      · exact (SubdiffusiveProcess.Lane4.continuous_cubeDilation z 0
          ((3 : ℝ) ^ (j + 2))).measurable
      · dsimp [T]
        rw [SubdiffusiveProcess.Lane4.map_cubeDilation_restrict z 0 hRj (by norm_num)]
        exact Measure.smul_absolutelyContinuous
    have hcomp := hqm.ae_eq_comp hphys
    have hQunit : Homogenization.openCubeSet Q ⊆
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d)) := by
      rw [hunit]
      exact hQ
    have hcompQ := ae_restrict_of_ae_restrict_of_subset hQunit hcomp
    have hcompQ' :
        (fun x : SpatialCoordinates d => aR.val (fun i => z i +
            (3 : ℝ) ^ (j + 2) * x i)) =ᵐ[volume.restrict (Homogenization.openCubeSet Q)]
          (fun x : SpatialCoordinates d => ar.val (fun i => z i +
            (3 : ℝ) ^ (j + 2) * x i)) := by
      have hT : T = fun x : SpatialCoordinates d =>
          fun i => z i + (3 : ℝ) ^ (j + 2) * x i := by
        funext x i
        simp [T, SubdiffusiveProcess.Lane4.cubeDilation]
      rw [hT] at hcompQ
      simpa only [Function.comp_apply] using hcompQ
    have hcompQmat :
        (fun x : SpatialCoordinates d =>
          Homogenization.scalarMatrix (d := d)
            (aR.val (fun i => z i + (3 : ℝ) ^ (j + 2) * x i))) =ᵐ[
          volume.restrict (Homogenization.openCubeSet Q)]
        (fun x : SpatialCoordinates d =>
          Homogenization.scalarMatrix (d := d)
            (ar.val (fun i => z i + (3 : ℝ) ^ (j + 2) * x i))) :=
      hcompQ'.fun_comp (fun v : ℝ => Homogenization.scalarMatrix (d := d) v)
    change ((E.chart z ((3 : ℝ) ^ m) hR aR z ((3 : ℝ) ^ (j + 2))).coeffOn Q).toCoeffField =ᵐ[
      volume.restrict (Homogenization.openCubeSet Q)]
      ((E.chart z ((3 : ℝ) ^ (j + 2)) hRj ar z ((3 : ℝ) ^ (j + 2))).coeffOn Q).toCoeffField
    exact Filter.EventuallyEq.trans hrootQ
      (Filter.EventuallyEq.trans hcompQmat (Filter.EventuallyEq.symm hinnerQ))
  change E.err z ((3 : ℝ) ^ m) hR aR z ((3 : ℝ) ^ (j + 2)) a0 s q =
    E.err z ((3 : ℝ) ^ (j + 2)) hRj ar z ((3 : ℝ) ^ (j + 2)) a0 s q
  by_cases hqtop : q = ⊤
  · calc
      E.err z ((3 : ℝ) ^ m) hR aR z ((3 : ℝ) ^ (j + 2)) a0 s q =
          (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity
            (Homogenization.originCube d 0) 0 s
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (E.chart z ((3 : ℝ) ^ m) hR aR z ((3 : ℝ) ^ (j + 2))) a0).toReal := by
        simpa only [if_pos hqtop] using
          (E.err_eq z ((3 : ℝ) ^ m) hR aR z ((3 : ℝ) ^ (j + 2)) hRj hsub
            s hs q hq a0 ha0)
      _ =
          (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity
            (Homogenization.originCube d 0) 0 s
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (E.chart z ((3 : ℝ) ^ (j + 2)) hRj ar z ((3 : ℝ) ^ (j + 2))) a0).toReal := by
        exact congrArg ENNReal.toReal
          (aux_lem_repair_err_good_scale_localization_error_infinity
            (Homogenization.originCube d 0) 0 s
            Homogenization.Book.Ch02.MultiscaleExponent.infinity a0 hchart)
      _ = E.err z ((3 : ℝ) ^ (j + 2)) hRj ar z ((3 : ℝ) ^ (j + 2)) a0 s q := by
        simpa only [if_pos hqtop] using
          (E.err_eq z ((3 : ℝ) ^ (j + 2)) hRj ar z ((3 : ℝ) ^ (j + 2)) hRj
            Set.Subset.rfl s hs q hq a0 ha0).symm
  · calc
      E.err z ((3 : ℝ) ^ m) hR aR z ((3 : ℝ) ^ (j + 2)) a0 s q =
          (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
            (Homogenization.originCube d 0) 0 s
            Homogenization.Book.Ch02.MultiscaleExponent.infinity q.toReal
            (E.chart z ((3 : ℝ) ^ m) hR aR z ((3 : ℝ) ^ (j + 2))) a0).toReal := by
        simpa only [if_neg hqtop] using
          (E.err_eq z ((3 : ℝ) ^ m) hR aR z ((3 : ℝ) ^ (j + 2)) hRj hsub
            s hs q hq a0 ha0)
      _ =
          (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
            (Homogenization.originCube d 0) 0 s
            Homogenization.Book.Ch02.MultiscaleExponent.infinity q.toReal
            (E.chart z ((3 : ℝ) ^ (j + 2)) hRj ar z ((3 : ℝ) ^ (j + 2))) a0).toReal := by
        exact congrArg ENNReal.toReal
          (aux_lem_repair_err_good_scale_localization_error
            (Homogenization.originCube d 0) 0 s
            Homogenization.Book.Ch02.MultiscaleExponent.infinity q.toReal a0 hchart)
      _ = E.err z ((3 : ℝ) ^ (j + 2)) hRj ar z ((3 : ℝ) ^ (j + 2)) a0 s q := by
        simpa only [if_neg hqtop] using
          (E.err_eq z ((3 : ℝ) ^ (j + 2)) hRj ar z ((3 : ℝ) ^ (j + 2)) hRj
            Set.Subset.rfl s hs q hq a0 ha0).symm

end Paper
