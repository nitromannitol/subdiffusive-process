import SubdiffusiveProcess.Paper.obl_ramp_threshold12_transfer
import SubdiffusiveProcess.Lane3.Forms
import Mathlib.Tactic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatioEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.RatioCollapse
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.SubunitTail
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffEllipticityCaps
import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CarrierComparison
import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.StabilityIndexCube


set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators

namespace Paper

theorem aux_obl_ramp_coarse_ellipticity_transfer_summable
    {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) (a₀ s : ℝ)
    (hs : 0 < s) :
    Summable (fun l : ℕ =>
      Homogenization.Book.Ch02.geometricWeight s 2 l *
        Real.rpow
          (Homogenization.Book.Ch02.scaleResponseAtScale Q
            (Q.scale - (l : ℤ)) .infinity F
            (Homogenization.scalarMatrix (d := d) a₀)) 2) := by
  let C : ℝ :=
    Homogenization.Book.Ch02.normalizedBlockResponseUniformBound Q F
      (Homogenization.scalarMatrix (d := d) a₀)
  let C₀ : ℝ := max C 0
  let H : ℕ → ℝ := fun l =>
    Real.rpow
      (Homogenization.Book.Ch02.scaleResponseAtScale Q
        (Q.scale - (l : ℤ)) .infinity F
        (Homogenization.scalarMatrix (d := d) a₀)) 2
  have hnonneg : ∀ l : ℕ, 0 ≤ H l := by
    intro l
    dsimp [H]
    exact Real.rpow_nonneg
      (Homogenization.Book.Ch02.scaleResponseAtScale_infinity_nonneg Q
        (sub_le_self _ (Int.natCast_nonneg l)) F
        (Homogenization.scalarMatrix (d := d) a₀)) _
  have hbound : ∀ l : ℕ, H l ≤ C₀ := by
    intro l
    have hT : 0 ≤
        Homogenization.Book.Ch02.scaleResponseAtScale Q
          (Q.scale - (l : ℤ)) .infinity F
          (Homogenization.scalarMatrix (d := d) a₀) :=
      Homogenization.Book.Ch02.scaleResponseAtScale_infinity_nonneg Q
        (sub_le_self _ (Int.natCast_nonneg l)) F
        (Homogenization.scalarMatrix (d := d) a₀)
    have hscale :=
      Homogenization.Book.Ch02.scaleResponseAtScale_infinity_le_uniform Q
        (sub_le_self _ (Int.natCast_nonneg l)) F
        (Homogenization.scalarMatrix (d := d) a₀)
    have hscaleC :
        Homogenization.Book.Ch02.scaleResponseAtScale Q
            (Q.scale - (l : ℤ)) .infinity F
            (Homogenization.scalarMatrix (d := d) a₀) ≤
          Real.rpow C (1 / 2 : ℝ) := by
      simpa only [C] using hscale
    have hH : H l =
        (Homogenization.Book.Ch02.scaleResponseAtScale Q
          (Q.scale - (l : ℤ)) .infinity F
          (Homogenization.scalarMatrix (d := d) a₀)) ^ 2 := by
      dsimp [H]
      simpa only [Homogenization.Book.Ch02.scaleResponseAtScale_infinity_eq] using
        (Real.rpow_two
          (Real.rpow
            (Homogenization.Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
              (Q.scale - (l : ℤ)) F
              (Homogenization.scalarMatrix (d := d) a₀)) (1 / 2 : ℝ)))
    by_cases hC : 0 ≤ C
    · have hsq :
          Real.rpow (Real.rpow C (1 / 2 : ℝ)) (2 : ℝ) = C := by
        calc
          Real.rpow (Real.rpow C (1 / 2 : ℝ)) (2 : ℝ) =
              Real.rpow C ((1 / 2 : ℝ) * 2) :=
            (Real.rpow_mul hC (1 / 2 : ℝ) 2).symm
          _ = C := by norm_num [Real.rpow_one]
      rw [hH]
      have hprod := mul_nonneg (sub_nonneg.mpr hscaleC)
        (add_nonneg hT (by exact hT.trans hscaleC))
      calc
        (Homogenization.Book.Ch02.scaleResponseAtScale Q
            (Q.scale - (l : ℤ)) .infinity F
            (Homogenization.scalarMatrix (d := d) a₀)) ^ 2 ≤
            (Real.rpow C (1 / 2 : ℝ)) ^ 2 := by nlinarith
        _ = C := by
          calc
            (Real.rpow C (1 / 2 : ℝ)) ^ 2 =
                Real.rpow (Real.rpow C (1 / 2 : ℝ)) (2 : ℝ) :=
              (Real.rpow_two _).symm
            _ = C := hsq
        _ = C₀ := (max_eq_left hC).symm
    · have hR : Real.rpow C (1 / 2 : ℝ) = 0 := by
        change C ^ (1 / 2 : ℝ) = 0
        rw [Real.rpow_def_of_nonpos (le_of_not_ge hC)]
        simp only [if_neg (ne_of_lt (lt_of_not_ge hC))]
        rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring,
          Real.cos_pi_div_two, mul_zero]
      have hT0 :
          Homogenization.Book.Ch02.scaleResponseAtScale Q
            (Q.scale - (l : ℤ)) .infinity F
            (Homogenization.scalarMatrix (d := d) a₀) = 0 := by
        linarith [hscale, hT]
      rw [hH, hT0]
      norm_num
      exact le_max_right _ _
  have hsum :=
    Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := (2 : ℝ)) (C := C₀) (by positivity) hnonneg hbound
  simpa only [H, C, C₀] using hsum

theorem aux_obl_ramp_coarse_ellipticity_transfer_anchor_error
    (d : ℕ) [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (L k : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hs : 0 < s)
    (hσ : 0 < tailCoefficientCubeAverage M L k
      (translatePotentialSample z omega)) :
    Ch02.HomogenizationErrorOnCube (originCube d (k : ℤ)) s
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (scalarMatrix (d := d)
          (tailCoefficientCubeAverage M L k
            (translatePotentialSample z omega))) ≤
      section6HomogenizationError M s L k omega z := by
  let Q := originCube d (k : ℤ)
  let F := aCutoffFamily M L (translatePotentialSample z omega)
  let alpha := tailCoefficientCubeAverage M L k
    (translatePotentialSample z omega)
  have hsum : Summable (fun l : ℕ =>
      Ch02.geometricWeight s 2 l *
        Real.rpow (Ch02.scaleResponseAtScale Q
          (Q.scale - (l : ℤ)) .infinity F
          (scalarMatrix (d := d) alpha)) 2) := by
    exact aux_obl_ramp_coarse_ellipticity_transfer_summable Q F alpha s hs
  have ha : ∀ R : Homogenization.TriadicCube d, (F.coeffOn R).IsSymmetric := by
    intro R
    exact (aCutoffTriadicData M L (translatePotentialSample z omega)).onCube R |>.isSymmetric
  have hpaper_le :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.paperHomogenizationError_le_ofReal_finite
      Q (by rfl) hs.le (by norm_num : (0 : ℝ) < 2) F ha hσ hsum
  have hraw :=
    Section6HarmonicApproximation.ofReal_homogenizationErrorOnCube_infinity_two_le_paper
      Q F ha hs hσ
  have hpaper_le' :
      paperHomogenizationError Q Q.scale s .infinity (.finite 2) F alpha ≤
        ENNReal.ofReal
          (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
            (scalarMatrix (d := d) alpha)) := by
    simpa only [Ch02.HomogenizationErrorOnCube] using hpaper_le
  have hEq :
      paperHomogenizationError Q Q.scale s .infinity (.finite 2) F alpha =
        ENNReal.ofReal
          (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
            (scalarMatrix (d := d) alpha)) := by
    apply le_antisymm
    · exact hpaper_le'
    · exact hraw
  have hfinite :
      paperHomogenizationError Q Q.scale s .infinity (.finite 2) F alpha ≠ ⊤ := by
    rw [hEq]
    exact ENNReal.ofReal_ne_top
  have hsection :
      section6HomogenizationError M s L k omega z =
        (paperHomogenizationError Q Q.scale s .infinity (.finite 2) F alpha).toReal := by
    rfl
  have hle :
      Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
          (scalarMatrix (d := d) alpha) ≤
        (paperHomogenizationError Q Q.scale s .infinity (.finite 2) F alpha).toReal := by
    have hOF :
        ENNReal.ofReal
            (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
              (scalarMatrix (d := d) alpha)) ≤
          ENNReal.ofReal
            (paperHomogenizationError Q Q.scale s .infinity (.finite 2) F alpha).toReal := by
      rw [ENNReal.ofReal_toReal hfinite]
      exact hraw
    exact (ENNReal.ofReal_le_ofReal_iff
      (ENNReal.toReal_nonneg :
        0 ≤ (paperHomogenizationError Q Q.scale s .infinity (.finite 2) F alpha).toReal)).mp hOF
  simpa only [Q, F, alpha, hsection] using hle

theorem aux_obl_ramp_coarse_ellipticity_transfer_local_error
    (d : ℕ) [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L m n : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x y z : Vec d)
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hD : translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x)
    (hanchor : Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) + 2))
        (s / 8) .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      section6HomogenizationError M (s / 8) L (n + 2) omega z) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample y omega))
        (scalarMatrix (d := d)
          (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
  let P : Homogenization.TriadicCube d := originCube d ((n : ℤ) - 2)
  let K : Homogenization.TriadicCube d := originCube d ((n : ℤ) + 2)
  let w : Vec d := y - z
  let A := aCutoffFamily M L (translatePotentialSample z omega)
  let A' := aCutoffFamily M L (translatePotentialSample y omega)
  let a : Homogenization.CoeffField d :=
    scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
      (translatePotentialSample z omega))
  let sigma : ℝ :=
    tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hrep : ∀ Q : Homogenization.TriadicCube d,
      (A.coeffOn Q).toCoeffField = a := by
    intro Q
    rfl
  have hcompact : IsCompact (closure (cubeSet K)) :=
    (isBounded_cubeSet K).isCompact_closure
  have hnonempty : (closure (cubeSet K)).Nonempty :=
    ⟨cubeCenter K, subset_closure (cubeCenter_mem_cubeSet K)⟩
  let a0 := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
    (translatePotentialSample z omega)
  have ha : Continuous a0 :=
    SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L
      (translatePotentialSample z omega)
  obtain ⟨xmin, hxmin, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty ha.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty ha.continuousOn
  have hTmeas : MeasurableSet (translateSet w (cubeSet P)) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet P).preimage
      (measurable_id.sub measurable_const)
  have hcontain : translateSet (y - z) (cubeSet P) ⊆ cubeSet K :=
    closedOffGridCube_subset_originAnchorParent hx hD
  have hEll : IsEllipticFieldOn (a0 xmin) (a0 xmax)
      (translateSet w (cubeSet P)) a := by
    constructor
    · have hmatrix : Continuous fun p : Vec d => scalarCoeffField a0 p :=
        ha.smul continuous_const
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      have hentry : Measurable fun p : Vec d => scalarCoeffField a0 p i j :=
        (continuous_apply j).comp ((continuous_apply i).comp hmatrix) |>.measurable
      exact Measurable.ite hTmeas hentry measurable_const
    · intro p hp
      have hpK : p ∈ closure (cubeSet K) := subset_closure (hcontain hp)
      have hlow : a0 xmin ≤ a0 p := hmin hpK
      have hupp : a0 p ≤ a0 xmax := hmax hpK
      exact (isEllipticMatrix_scalarMatrix
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L
          (translatePotentialSample z omega) p)).mono
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L
            (translatePotentialSample z omega) xmin) hlow hupp
  have hstab := offGridErrorFunctional_le_slot
    (w := w) (P := P) (K := K) A
      (scalarMatrix (d := d) sigma) hs0 (hs.2.trans (by norm_num)) hrep hEll hcontain
  have hscale : (((K.scale - P.scale).toNat : ℕ) : ℝ) = 4 := by
    change (((((n : ℤ) + 2) - ((n : ℤ) - 2)).toNat : ℕ) : ℝ) = 4
    rw [show ((n : ℤ) + 2) - ((n : ℤ) - 2) = 4 by ring]
    rfl
  rw [hscale] at hstab
  have hframe := offGridErrorFunctional_eq_homogenizationErrorOnCube_translate
    w P (by linarith only [hs0] : 0 < s / 6) A' a
      (aCutoffFamily_coeffField_translate_sub M L omega y z)
      (scalarMatrix (d := d) sigma)
  have hlocal : Ch02.HomogenizationErrorOnCube P (s / 6)
      .infinity (.finite 2) A' (scalarMatrix (d := d) sigma) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
    have hparent' : Ch02.HomogenizationErrorOnCube K (s / 8)
        .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤
        section6HomogenizationError M (s / 8) L (n + 2) omega z := by
      simpa [K, A, sigma,
        Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] using hanchor
    rw [← hframe]
    exact hstab.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hparent' (Real.rpow_nonneg (by norm_num) _))
      (Real.sqrt_nonneg _))
  simpa only [P, A', sigma] using hlocal



theorem obl_ramp_coarse_ellipticity_transfer
    (d : ℕ) [NeZero d]
    (hregularities : Paper.product_threshold_regularities d 12) :
    ∃ E₀ B : ℝ, 0 < E₀ ∧ 0 < B ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
      ∀ L m n : ℕ, ∀ z x y : Vec d,
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        x ∈ truncatedCube d m (n - 3) z →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        omega ∈ Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8) →
        let Q := originCube d ((n : ℤ) - 2)
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
              (scalarMatrix (d := d) sigma) ≤ E₀ ∧
          sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2) A ≤ B ∧
          sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B ∧
          Ch02.LambdaS Q (1 / 2) A ≤ B * sigma ∧
          (Ch02.lambdaS Q (s / 3) A)⁻¹ ≤ B * sigma⁻¹ ∧
          Ch02.lambdaS Q (s / 3) A ≤ B * sigma ∧
          Ch02.ThetaRatio Q (1 / 2) (s / 3) A ≤ B ^ (2 : ℕ) := by
  obtain ⟨Cerr, hCerr, hregularityError⟩ := hregularities.2.2.2
  let E₀ : ℝ := Real.sqrt (192 * (d : ℝ)) * (3 * Cerr)
  let B : ℝ := 2 * (d : ℝ) * (E₀ ^ 2 + 1)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hE₀ : 0 < E₀ := by
    dsimp [E₀]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨E₀, B, hE₀, hB, ?_⟩
  intro M s hs hsmall L m n z x y omega hx hsub homega
  dsimp only
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hs8 : 0 < s / 8 := by positivity
  have hs8range : s / 8 ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) := by
    constructor
    · linarith only [hs.1]
    · linarith only [hs.2]
  have hepsRange : (1 : ℝ) ∈ Set.Icc ((s / 8)⁻¹ * M.delta ^ 2) 1 := by
    constructor
    · rw [inv_mul_le_iff₀ hs8]
      nlinarith only [hs.1]
    · norm_num
  have hsec := hregularityError M L (s / 8) hs8range hsmall 1 hepsRange
      (n + 2) z omega
  have hsecCap :
      section6HomogenizationError M (s / 8) L (n + 2) omega z ≤ Cerr := by
    rw [Section6ExcessDecay.indicatorValue_of_mem homega] at hsec
    simpa using hsec.2
  have hsigma0 : 0 < tailCoefficientCubeAverage M L (n + 2)
      (translatePotentialSample z omega) :=
    tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hanchor :=
    aux_obl_ramp_coarse_ellipticity_transfer_anchor_error (d := d)
      M (s / 8) L (n + 2)
      omega z hs8 hsigma0
  let P : Homogenization.TriadicCube d := originCube d ((n : ℤ) - 2)
  let K : Homogenization.TriadicCube d := originCube d ((n : ℤ) + 2)
  let w : Vec d := y - z
  let A0 := aCutoffFamily M L (translatePotentialSample z omega)
  let A' := aCutoffFamily M L (translatePotentialSample y omega)
  let a : Homogenization.CoeffField d :=
    scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
      (translatePotentialSample z omega))
  let sigma0 : ℝ :=
    tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hrep : ∀ R : Homogenization.TriadicCube d,
      (A0.coeffOn R).toCoeffField = a := by
    intro R
    rfl
  have hcompact : IsCompact (closure (cubeSet K)) :=
    (isBounded_cubeSet K).isCompact_closure
  have hnonempty : (closure (cubeSet K)).Nonempty :=
    ⟨cubeCenter K, subset_closure (cubeCenter_mem_cubeSet K)⟩
  have hTmeas : MeasurableSet (translateSet w (cubeSet P)) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet P).preimage
      (measurable_id.sub measurable_const)
  have hcontain : translateSet w (cubeSet P) ⊆ cubeSet K :=
    closedOffGridCube_subset_originAnchorParent hx hsub
  let a0 := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
    (translatePotentialSample z omega)
  have ha : Continuous a0 :=
    SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L
      (translatePotentialSample z omega)
  obtain ⟨xmin, hxmin, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty ha.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty ha.continuousOn
  have hEll : IsEllipticFieldOn (a0 xmin) (a0 xmax)
      (translateSet w (cubeSet P)) a := by
    constructor
    · have hmatrix : Continuous fun p : Vec d => scalarCoeffField a0 p :=
        ha.smul continuous_const
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      have hentry : Measurable fun p : Vec d => scalarCoeffField a0 p i j :=
        (continuous_apply j).comp ((continuous_apply i).comp hmatrix) |>.measurable
      exact Measurable.ite hTmeas hentry measurable_const
    · intro p hp
      have hpK : p ∈ closure (cubeSet K) := subset_closure (hcontain hp)
      have hlow : a0 xmin ≤ a0 p := hmin hpK
      have hupp : a0 p ≤ a0 xmax := hmax hpK
      exact (isEllipticMatrix_scalarMatrix
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L
          (translatePotentialSample z omega) p)).mono
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L
            (translatePotentialSample z omega) xmin) hlow hupp
  have hstab := offGridErrorFunctional_le_slot
    (w := w) (P := P) (K := K) A0
      (scalarMatrix (d := d) sigma0) hs0 (hs.2.trans (by norm_num)) hrep hEll hcontain
  have hscale : (((K.scale - P.scale).toNat : ℕ) : ℝ) = 4 := by
    change (((((n : ℤ) + 2) - ((n : ℤ) - 2)).toNat : ℕ) : ℝ) = 4
    rw [show ((n : ℤ) + 2) - ((n : ℤ) - 2) = 4 by ring]
    rfl
  rw [hscale] at hstab
  have hframe := offGridErrorFunctional_eq_homogenizationErrorOnCube_translate
    w P (by linarith only [hs0] : 0 < s / 6) A' a
      (aCutoffFamily_coeffField_translate_sub M L omega y z)
      (scalarMatrix (d := d) sigma0)
  have hlocal : Ch02.HomogenizationErrorOnCube P (s / 6)
      .infinity (.finite 2) A' (scalarMatrix (d := d) sigma0) ≤
      Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z) := by
    have hparent' : Ch02.HomogenizationErrorOnCube K (s / 8)
        .infinity (.finite 2) A0 (scalarMatrix (d := d) sigma0) ≤
        section6HomogenizationError M (s / 8) L (n + 2) omega z := by
      simpa [K, A0, sigma0,
        Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] using hanchor
    rw [← hframe]
    exact hstab.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hparent' (Real.rpow_nonneg (by norm_num) _))
      (Real.sqrt_nonneg _))
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hexp : (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ 3 := by
    calc
      (3 : ℝ) ^ (s / 8 * (4 : ℝ)) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hs.2])
      _ = 3 := by norm_num
  have hsec0 : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
    ENNReal.toReal_nonneg
  have hscaled :
      (3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z ≤
        3 * Cerr := by
    calc
      (3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z ≤
          3 * section6HomogenizationError M (s / 8) L (n + 2) omega z :=
        mul_le_mul_of_nonneg_right hexp hsec0
      _ ≤ 3 * Cerr :=
        mul_le_mul_of_nonneg_left hsecCap (by norm_num)
  have hlocalCap :
      Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma) ≤ E₀ := by
    dsimp only [Q, A, sigma] at hlocal ⊢
    refine hlocal.trans ?_
    exact mul_le_mul_of_nonneg_left hscaled (Real.sqrt_nonneg _)
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    convert h using 1
  have hcaps := localBoundaryEllipticityCaps_of_errorCap Q A hs0 hs.2 hsigma hlocalCap
  simpa only [Q, A, sigma, B, E₀] using ⟨hlocalCap, hcaps⟩

end Paper
