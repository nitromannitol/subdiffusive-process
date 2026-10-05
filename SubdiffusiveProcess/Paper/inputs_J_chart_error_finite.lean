module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CarrierComparison

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

private theorem aux_inputs_J_chart_error_finite_scalar_symmetric
    {d : ℕ} (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (b : Homogenization.Vec d → ℝ)
    (hF : ∀ Q : Homogenization.TriadicCube d,
      Homogenization.openCubeSet Q ⊆
          Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
        (F.coeffOn Q).toCoeffField x =
          Homogenization.scalarMatrix (b x))
    {Q : Homogenization.TriadicCube d}
    (hQ : Homogenization.openCubeSet Q ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    Homogenization.Book.Ch02.CoeffOn.IsSymmetric (F.coeffOn Q) := by
  change ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
    ((F.coeffOn Q).toCoeffField x).IsSymm
  filter_upwards [hF Q hQ] with x hx
  rw [hx]
  exact Homogenization.scalarMatrix_isSymm _

private theorem aux_inputs_J_chart_error_finite_scale_response
    {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hSymm : ∀ R : Homogenization.TriadicCube d,
      R ∈ Homogenization.descendantsAtScale Q k →
        (F.coeffOn R).IsSymmetric)
    {alpha : ℝ} (halpha : 0 < alpha) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q k .infinity F alpha ≤
      ENNReal.ofReal
        (Homogenization.Book.Ch02.scaleResponseAtScale Q k .infinity F
          (Homogenization.scalarMatrix alpha)) := by
  have hbdd : BddAbove
      ((fun R : Homogenization.TriadicCube d =>
        Homogenization.Book.Ch02.normalizedBlockResponseMax R F
          (Homogenization.scalarMatrix alpha)) ''
        ((↑(Homogenization.descendantsAtScale Q k) :
          Set (Homogenization.TriadicCube d)))) :=
    ((Homogenization.descendantsAtScale Q k).finite_toSet.image _).bddAbove
  have hbase : SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
      Q k F alpha ≤ ENNReal.ofReal
        (Homogenization.Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          Q k F (Homogenization.scalarMatrix alpha)) := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale]
    refine iSup_le ?_
    rintro ⟨R, hR⟩
    rw [paperScalarProbeMax_eq_ofReal_normalizedBlockResponseMax
      R F (hSymm R hR) halpha]
    refine ENNReal.ofReal_le_ofReal ?_
    exact le_csSup hbdd ⟨R, hR, rfl⟩
  have hnonneg : 0 ≤
      Homogenization.Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        Q k F (Homogenization.scalarMatrix alpha) :=
    Homogenization.Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg
      Q hk F _
  have hpow := ENNReal.rpow_le_rpow hbase
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
  rw [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale,
    Homogenization.Book.Ch02.scaleResponseAtScale]
  refine le_trans hpow (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg hnonneg
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]
  rfl

private theorem aux_inputs_J_chart_error_finite_finite_ne_top
    {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d) {n : ℤ}
    (hn : n ≤ Q.scale) {s q : ℝ} (hs : 0 < s) (hq : 0 < q)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hSymm : ∀ (k : ℤ), k ≤ Q.scale → ∀ R : Homogenization.TriadicCube d,
      R ∈ Homogenization.descendantsAtScale Q k →
        (F.coeffOn R).IsSymmetric)
    {alpha : ℝ} (halpha : 0 < alpha) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite Q n s
      Homogenization.Book.Ch02.MultiscaleExponent.infinity q F alpha ≠ ⊤ := by
  let C : ℝ := Real.rpow
    (Homogenization.Book.Ch02.normalizedBlockResponseUniformBound Q F
      (Homogenization.scalarMatrix alpha)) (1 / 2 : ℝ)
  have hTnonneg : ∀ l : ℕ,
      0 ≤ Homogenization.Book.Ch02.scaleResponseAtScale Q
        (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha) := by
    intro l
    exact Homogenization.Book.Ch02.scaleResponseAtScale_infinity_nonneg Q
      ((sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn) F _
  have hTbound : ∀ l : ℕ,
      Homogenization.Book.Ch02.scaleResponseAtScale Q
        (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha) ≤ C := by
    intro l
    simpa [C] using
      Homogenization.Book.Ch02.scaleResponseAtScale_infinity_le_uniform Q
        ((sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn) F _
  have hsumOld : Summable fun l : ℕ =>
      Homogenization.Book.Ch02.geometricWeight s q l *
        Real.rpow
          (Homogenization.Book.Ch02.scaleResponseAtScale Q
            (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha)) q := by
    refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (C := Real.rpow C q) (mul_pos hs hq) ?_ ?_
    · intro l
      exact Real.rpow_nonneg (hTnonneg l) q
    · intro l
      exact Real.rpow_le_rpow (hTnonneg l) (hTbound l) hq.le
  have hsum : Summable fun l : ℕ =>
      Homogenization.Book.Ch02.geometricWeight s q l *
        Real.rpow
          (Homogenization.Book.Ch02.scaleResponseAtScale Q
            (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha)) q := by
    simpa [Homogenization.Book.Ch02.geometricWeight_eq_old] using hsumOld
  have hT : ∀ l : ℕ,
      0 ≤ Homogenization.Book.Ch02.scaleResponseAtScale Q
        (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha) := hTnonneg
  have hterm : ∀ l : ℕ,
      0 ≤ Homogenization.Book.Ch02.geometricWeight s q l *
        Real.rpow
          (Homogenization.Book.Ch02.scaleResponseAtScale Q
            (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha)) q := by
    intro l
    exact mul_nonneg
      (Homogenization.geometricWeight_nonneg (s := s) (q := q) l
        (le_of_lt (mul_pos hs hq)))
      (Real.rpow_nonneg (hT l) q)
  have hpointwise : ∀ l : ℕ,
      ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s q l) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q
            (n - (l : ℤ)) .infinity F alpha ^ q ≤
        ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s q l *
          Real.rpow
            (Homogenization.Book.Ch02.scaleResponseAtScale Q
              (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha)) q) := by
    intro l
    have hk : n - (l : ℤ) ≤ Q.scale :=
      (sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn
    have hscale := aux_inputs_J_chart_error_finite_scale_response Q hk F
      (fun R hR => hSymm (n - (l : ℤ)) hk R hR) halpha
    have hpow := ENNReal.rpow_le_rpow hscale hq.le
    have hconv :
        ENNReal.ofReal
            (Homogenization.Book.Ch02.scaleResponseAtScale Q
              (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha)) ^ q =
          ENNReal.ofReal (Real.rpow
            (Homogenization.Book.Ch02.scaleResponseAtScale Q
              (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha)) q) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (hT l) hq.le]
      rfl
    rw [hconv] at hpow
    have hweight : 0 ≤ Homogenization.Book.Ch02.geometricWeight s q l :=
      Homogenization.geometricWeight_nonneg (s := s) (q := q) l
        (le_of_lt (mul_pos hs hq))
    calc
      ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s q l) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q
            (n - (l : ℤ)) .infinity F alpha ^ q ≤
        ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s q l) *
          ENNReal.ofReal (Real.rpow
            (Homogenization.Book.Ch02.scaleResponseAtScale Q
              (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha)) q) :=
          mul_le_mul_of_nonneg_left hpow (by exact bot_le)
      _ = ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s q l *
          Real.rpow
            (Homogenization.Book.Ch02.scaleResponseAtScale Q
              (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha)) q) :=
          (ENNReal.ofReal_mul hweight).symm
  have hsumle :
      (∑' l : ℕ,
        ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s q l) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q
            (n - (l : ℤ)) .infinity F alpha ^ q) ≤
        ENNReal.ofReal (∑' l : ℕ,
          Homogenization.Book.Ch02.geometricWeight s q l *
            Real.rpow
              (Homogenization.Book.Ch02.scaleResponseAtScale Q
                (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha)) q) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hterm hsum]
    exact ENNReal.tsum_le_tsum hpointwise
  have houter := ENNReal.rpow_le_rpow hsumle
    (by positivity : (0 : ℝ) ≤ 1 / q)
  have hcap :
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite Q n s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity q F alpha ≤
        ENNReal.ofReal (Real.rpow
          (∑' l : ℕ,
            Homogenization.Book.Ch02.geometricWeight s q l *
              Real.rpow
                (Homogenization.Book.Ch02.scaleResponseAtScale Q
                  (n - (l : ℤ)) .infinity F (Homogenization.scalarMatrix alpha)) q)
          (1 / q)) := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite]
    refine le_trans houter (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg hterm)
      (by positivity : (0 : ℝ) ≤ 1 / q)]
    rfl
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcap

theorem inputs_J_chart_error_finite (d : ℕ) (hd : 2 ≤ d) (chart : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    PositiveCoefficient (centeredCube z r hr) →
      SpatialCoordinates d → ℝ →
        Homogenization.Book.Ch02.TriadicCoeffFamily d)) (hchart : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ Q : Homogenization.TriadicCube d,
        Homogenization.openCubeSet Q ⊆
          Homogenization.openCubeSet (Homogenization.originCube d 0) →
        ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
          ((chart z r hr a w r').coeffOn Q).toCoeffField x =
            Homogenization.scalarMatrix (a.val (fun i => w i + r' * x i)))) :
    (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → ∀ q : ℝ≥0∞, 1 ≤ q →
      ∀ a0 : ℝ, 0 < a0 →
      let e : ℝ≥0∞ :=
        if q = ⊤ then
          SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity
            (Homogenization.originCube d 0) 0 s
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (chart z r hr a w r') a0
        else
          SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
            (Homogenization.originCube d 0) 0 s
            Homogenization.Book.Ch02.MultiscaleExponent.infinity q.toReal
            (chart z r hr a w r') a0
      e < ⊤) := by
  let : NeZero d := ⟨by omega⟩
  intro z r hr a w r' hr' hsub s hs q hq a0 ha0
  let Q0 : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let F : Homogenization.Book.Ch02.TriadicCoeffFamily d := chart z r hr a w r'
  let b : Homogenization.Vec d → ℝ := fun x => a.val (fun i => w i + r' * x i)
  have hQ0scale : Q0.scale = 0 := by
    simp [Q0, Homogenization.originCube]
  have hSymm : ∀ (k : ℤ), k ≤ Q0.scale →
      ∀ R : Homogenization.TriadicCube d,
        R ∈ Homogenization.descendantsAtScale Q0 k →
          (F.coeffOn R).IsSymmetric := by
    intro k hk R hR
    have hRsub : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet Q0 :=
      Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk hR
    have hRroot : Homogenization.openCubeSet R ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0) := by
      simpa [Q0] using hRsub
    exact aux_inputs_J_chart_error_finite_scalar_symmetric F b
      (fun T hT => hchart z r hr a w r' hr' hsub T hT) hRroot
  by_cases hqtop : q = ⊤
  · have hU : 0 ≤ Real.rpow
        (Homogenization.Book.Ch02.normalizedBlockResponseUniformBound Q0 F
          (Homogenization.scalarMatrix a0)) (1 / 2 : ℝ) := by
      have hnonneg := Homogenization.Book.Ch02.scaleResponseAtScale_infinity_nonneg
        Q0 (by omega : (0 : ℤ) ≤ Q0.scale) F (Homogenization.scalarMatrix a0)
      have hbound := Homogenization.Book.Ch02.scaleResponseAtScale_infinity_le_uniform
        Q0 (by omega : (0 : ℤ) ≤ Q0.scale) F (Homogenization.scalarMatrix a0)
      exact hnonneg.trans hbound
    have herror :
        SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity Q0 0 s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity F a0 ≤
            ENNReal.ofReal (Real.rpow
              (Homogenization.Book.Ch02.normalizedBlockResponseUniformBound Q0 F
                (Homogenization.scalarMatrix a0)) (1 / 2 : ℝ)) := by
      rw [SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity]
      refine iSup_le ?_
      intro l
      have hk : (0 : ℤ) - (l : ℤ) ≤ Q0.scale := by omega
      have hscale := aux_inputs_J_chart_error_finite_scale_response Q0 hk F
        (fun R hR => hSymm (0 - (l : ℤ)) hk R hR) ha0
      have hTbound :
          Homogenization.Book.Ch02.scaleResponseAtScale Q0
            (0 - (l : ℤ)) .infinity F (Homogenization.scalarMatrix a0) ≤
          Real.rpow
            (Homogenization.Book.Ch02.normalizedBlockResponseUniformBound Q0 F
              (Homogenization.scalarMatrix a0)) (1 / 2 : ℝ) :=
        Homogenization.Book.Ch02.scaleResponseAtScale_infinity_le_uniform Q0 hk F _
      have hweightReal : Real.rpow (3 : ℝ) (-s * (l : ℝ)) ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        have hl : 0 ≤ (l : ℝ) := by exact_mod_cast Nat.zero_le l
        nlinarith [hs.1, hl]
      have hweight : ENNReal.ofReal (Real.rpow (3 : ℝ) (-s * (l : ℝ))) ≤ 1 :=
        ENNReal.ofReal_le_one.mpr hweightReal
      have hpaper :
          SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q0
            (0 - (l : ℤ)) .infinity F a0 ≤
          ENNReal.ofReal
            (Homogenization.Book.Ch02.scaleResponseAtScale Q0
              (0 - (l : ℤ)) .infinity F (Homogenization.scalarMatrix a0)) := hscale
      have hpaperBound :
          SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q0
            (0 - (l : ℤ)) .infinity F a0 ≤
          ENNReal.ofReal (Real.rpow
            (Homogenization.Book.Ch02.normalizedBlockResponseUniformBound Q0 F
              (Homogenization.scalarMatrix a0)) (1 / 2 : ℝ)) :=
        hpaper.trans (ENNReal.ofReal_le_ofReal hTbound)
      calc
        ENNReal.ofReal (Real.rpow (3 : ℝ) (-s * (l : ℝ))) *
            SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q0
              (0 - (l : ℤ)) .infinity F a0 ≤
          1 * ENNReal.ofReal (Real.rpow
            (Homogenization.Book.Ch02.normalizedBlockResponseUniformBound Q0 F
              (Homogenization.scalarMatrix a0)) (1 / 2 : ℝ)) := by
                exact mul_le_mul hweight hpaperBound (by exact bot_le) (by norm_num)
        _ = ENNReal.ofReal (Real.rpow
              (Homogenization.Book.Ch02.normalizedBlockResponseUniformBound Q0 F
                (Homogenization.scalarMatrix a0)) (1 / 2 : ℝ)) := by simp
    have hne :
        SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity Q0 0 s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity F a0 ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top herror
    simpa [hqtop] using (lt_top_iff_ne_top.mpr hne)
  · have hqzero : q ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hq)
    have hqreal : 0 < q.toReal := ENNReal.toReal_pos hqzero hqtop
    have hn : (0 : ℤ) ≤ Q0.scale := by omega
    have hne :
        SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite Q0 0 s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity q.toReal F a0 ≠ ⊤ :=
      aux_inputs_J_chart_error_finite_finite_ne_top Q0 hn hs.1 hqreal F
        hSymm ha0
    simpa [hqtop] using (lt_top_iff_ne_top.mpr hne)

end SubdiffusiveProcess.Paper
