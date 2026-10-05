module

public import SubdiffusiveProcess.Paper.product_threshold_regularities
public import SubdiffusiveProcess.Paper.obl_ramp_site_inputs
public import SubdiffusiveProcess.Paper.obl_ramp_threshold12_transfer
public import SubdiffusiveProcess.Paper.obl_ramp_coarse_ellipticity_transfer
public import SubdiffusiveProcess.ResponseMoments.Forms
public import Mathlib.Tactic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatioEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.RatioCollapse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.SubunitTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffEllipticityCaps

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators

namespace SubdiffusiveProcess.Paper

lemma aux_obl_ramp_ramp (x : ℝ) :
    (if 12 < x then (1 : ℝ) else 0) ≤ ramp 6 12 x ∧
    ramp 6 12 x ≤ (if 6 < x then (1 : ℝ) else 0) ∧
    0 ≤ ramp 6 12 x ∧
    ramp 6 12 x ≤ 1 := by
  unfold ramp
  have hnonneg : 0 ≤ max 0 ((x - 6) / (12 - 6)) := le_max_left _ _
  have hleone : min 1 (max 0 ((x - 6) / (12 - 6))) ≤ 1 :=
    min_le_left _ _
  by_cases h12 : 12 < x
  · have hratio : 1 ≤ (x - 6) / (12 - 6) := by
      norm_num
      linarith
    have hmax : 1 ≤ max 0 ((x - 6) / (12 - 6)) :=
      hratio.trans (le_max_right _ _)
    have h6 : 6 < x := by linarith
    rw [min_eq_left hmax]
    simp [h12, h6]
  · by_cases h6 : 6 < x
    · simp [h12, h6, hnonneg, hleone]
    · have hratio : (x - 6) / (12 - 6) ≤ 0 := by
        norm_num
        linarith
      rw [max_eq_left hratio]
      simp [h12, h6]

lemma aux_obl_ramp_exp_bound (s tau D : ℝ) (_hs : 0 < s)
    (htau : tau ^ 2 ≤ s * Real.log 3 / 16) (hD : 0 ≤ D) :
    Real.exp (tau ^ 2 * D) ≤ (3 : ℝ) ^ (s * D / 16) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  apply Real.exp_le_exp.mpr
  calc
    tau ^ 2 * D ≤ (s * Real.log 3 / 16) * D :=
      mul_le_mul_of_nonneg_right htau hD
    _ = Real.log 3 * (s * D / 16) := by ring

lemma aux_obl_ramp_exponent_identity (s D : ℝ) :
    (3 : ℝ) ^ (-(3 * s * D / 2)) * ((3 : ℝ) ^ (3 * s * D / 16)) ^ 2 *
        (3 : ℝ) ^ (s * D / 8) = (3 : ℝ) ^ (-s * D) := by
  calc
    (3 : ℝ) ^ (-(3 * s * D / 2)) * ((3 : ℝ) ^ (3 * s * D / 16)) ^ 2 *
          (3 : ℝ) ^ (s * D / 8) =
        (3 : ℝ) ^ (-(3 * s * D / 2)) *
          ((3 : ℝ) ^ (3 * s * D / 16) * (3 : ℝ) ^ (3 * s * D / 16)) *
          (3 : ℝ) ^ (s * D / 8) := by rw [pow_two]
    _ = (3 : ℝ) ^ (-(3 * s * D / 2) + (3 * s * D / 16 + 3 * s * D / 16)) *
          (3 : ℝ) ^ (s * D / 8) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ = (3 : ℝ) ^
          (-(3 * s * D / 2) + (3 * s * D / 16 + 3 * s * D / 16) +
            s * D / 8) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ = (3 : ℝ) ^ (-s * D) := by congr 1 ; ring



theorem obl_ramp
    (d : ℕ) [NeZero d] :
    _root_.SubdiffusiveProcess.Paper.product_threshold_regularities d 12 ∧
    (∀ x : ℝ,
      (if 12 < x then (1 : ℝ) else 0) ≤ ramp 6 12 x ∧
      ramp 6 12 x ≤ (if 6 < x then (1 : ℝ) else 0) ∧
      0 ≤ ramp 6 12 x ∧
      ramp 6 12 x ≤ 1) ∧
    (∀ s tau : ℝ, 0 < s → tau ^ 2 ≤ s * Real.log 3 / 16 →
      ∀ D : ℝ, 0 ≤ D →
        Real.exp (tau ^ 2 * D) ≤ (3 : ℝ) ^ (s * D / 16)) ∧
    (∀ s D : ℝ,
      (3 : ℝ) ^ (-(3 * s * D / 2)) * ((3 : ℝ) ^ (3 * s * D / 16)) ^ 2 *
          (3 : ℝ) ^ (s * D / 8) = (3 : ℝ) ^ (-s * D)) ∧
    (∃ CB : ℝ, 0 < CB ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
        _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 →
        ∀ L m : ℕ, m ≤ L → ∀ w : Vec d, ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          omega ∈ _root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m w 1 s →
          let eta := translatePotentialSample w omega
          -- A. summability of the tail of shell-gradients
          Summable (fun j : ℕ =>
            if m ≤ j then (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (eta j))
            else 0) ∧
          -- B. finiteness (BddAbove) of the exact product-sum before real sSup
          (∀ j : ℕ,
            BddAbove ((fun x : Vec d =>
              |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |eta i x|) +
                ∏' i : ℕ,
                  if m + j ≤ i then Real.exp (4 * |eta i x - eta i 0|) else 1|) ''
              translatedCube d (m + 1 + j) 0)) ∧
          -- C. long-wavelength normalization deviation bound
          longRatioDeviation M L m eta ≤ CB * min 1 (longRatioGradientTail m eta) ∧
          -- D. intermediate-cutoff bounds on all n ≤ m and contained cells
          (∀ n : ℕ, n ≤ m → ∀ z : Vec d,
            translatedCube d n z ⊆ cube d m →
            BddAbove ((fun x : Vec d => |combinedCoefficientRatio M L m n eta z x - 1|) ''
              cube d n) ∧
            BddAbove ((fun x : Vec d => |combinedCoefficientRatioInv M L m n eta z x - 1|) ''
              cube d n) ∧
            Real.exp (supNormOn (cube d n)
                (shellBlock m n (translatePotentialSample z eta))) ≤
              12 * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)) / 8) ∧
            |normalizerLogError M m n| ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P *
              ((m : ℝ) - (n : ℝ)) ∧
            Real.exp |normalizerLogError M m n| ≤
              (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)) / 16) ∧
            supNormOn (cube d n)
                (fun x => combinedCoefficientRatio M L m n eta z x - 1) +
              supNormOn (cube d n)
                (fun x => combinedCoefficientRatioInv M L m n eta z x - 1) ≤
              CB * (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
                min 1 (longRatioGradientTail m eta +
                  supNormOn (cube d n) (shellBlock m n (translatePotentialSample z eta)) +
                  _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) - (n : ℝ)))) ∧
          -- E. below-unit-scale contribution
          Real.exp (supNormOn (cube d m) (fullShellBlock m eta)) ≤
            12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) ∧
          |subunitLogError M m| ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1) ∧
          (∀ x ∈ cube d m,
            let b := fullShellBlock m eta x + subunitLogError M m
            Real.exp b + Real.exp (-b) - 2 ≤ b ^ 2 * Real.exp |b| ∧
            (_root_.SubdiffusiveProcess.Model.aCutoff M L eta x / tailCoefficientCubeAverage M L m eta - 1) ^ 2 +
                (tailCoefficientCubeAverage M L m eta / _root_.SubdiffusiveProcess.Model.aCutoff M L eta x - 1) ^ 2 ≤
              (CB * (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
                    (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) *
                min 1 (longRatioGradientTail m eta +
                  supNormOn (cube d m) (fullShellBlock m eta) +
                  _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1))) ^ 2)) ∧
    -- 6. two-sided coarse ellipticity conversion (paper e.bound.Lambdas.by.Es)
    (∃ E₀ B : ℝ, 0 < E₀ ∧ 0 < B ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ (s / 8) * Real.log 3 / 16 →
      ∀ L m n : ℕ, ∀ z x y : Vec d,
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        x ∈ truncatedCube d m (n - 3) z →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        omega ∈ _root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) (n + 2) z 1 (s / 8) →
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
          Ch02.ThetaRatio Q (1 / 2) (s / 3) A ≤ B ^ (2 : ℕ)) := by
  have hsites := obl_ramp_site_inputs d
  have hregularities := obl_ramp_threshold12_transfer d
  have hcoarse := obl_ramp_coarse_ellipticity_transfer d hregularities
  have hramp : ∀ x : ℝ,
      (if 12 < x then (1 : ℝ) else 0) ≤ ramp 6 12 x ∧
      ramp 6 12 x ≤ (if 6 < x then (1 : ℝ) else 0) ∧
      0 ≤ ramp 6 12 x ∧
      ramp 6 12 x ≤ 1 := by
    intro x
    exact aux_obl_ramp_ramp x
  have hexp : ∀ s tau : ℝ, 0 < s → tau ^ 2 ≤ s * Real.log 3 / 16 →
      ∀ D : ℝ, 0 ≤ D →
        Real.exp (tau ^ 2 * D) ≤ (3 : ℝ) ^ (s * D / 16) := by
    intro s tau hs htau D hD
    exact aux_obl_ramp_exp_bound s tau D hs htau hD
  have hpow : ∀ s D : ℝ,
      (3 : ℝ) ^ (-(3 * s * D / 2)) * ((3 : ℝ) ^ (3 * s * D / 16)) ^ 2 *
          (3 : ℝ) ^ (s * D / 8) = (3 : ℝ) ^ (-s * D) := by
    intro s D
    exact aux_obl_ramp_exponent_identity s D
  obtain ⟨CB, hCB, hsites'⟩ := hsites
  refine ⟨hregularities, hramp, hexp, hpow, ?_, hcoarse⟩
  refine ⟨CB, hCB, ?_⟩
  intro M s hs hsmall L m hmL w omega homega
  dsimp
  have homega' := homega
  change 0 < (12 : ℝ) ∧ 0 < s ∧ s ≤ 1 ∧ 0 < (1 : ℝ) ∧ (1 : ℝ) ≤ 1 ∧
      SubdiffusiveProcess.CoarseGrainingVocab.GoodFieldOne m w 1 s omega ∧
      (∀ j : ℕ,
        (∀ x ∈ translatedCube d (m + 1 + j) w,
          Multipliable (fun i : ℕ =>
            if m + j ≤ i then Real.exp (4 * |omega i x - omega i w|) else 1)) ∧
        BddAbove ((fun x : Vec d =>
          |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
            ∏' i : ℕ,
              if m + j ≤ i then Real.exp (4 * |omega i x - omega i w|) else 1|) ''
          translatedCube d (m + 1 + j) w) ∧
        supNormOn (translatedCube d (m + 1 + j) w) (fun x ↦
          (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
            ∏' i : ℕ,
              if m + j ≤ i then Real.exp (4 * |omega i x - omega i w|) else 1) ≤
          (12 : ℝ) * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)) ∧
      SubdiffusiveProcess.CoarseGrainingVocab.GoodResponse M (some L) m w 1 s omega at homega'
  rcases homega' with ⟨_, _, _, _, _, hfield, hprod, _⟩
  let eta := translatePotentialSample w omega
  have hfield0 : SubdiffusiveProcess.CoarseGrainingVocab.GoodFieldOne m 0 1 s eta := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.goodFieldOne_translatePotentialSample]
    simpa using hfield
  have hA : Summable (fun j : ℕ =>
      if m ≤ j then (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (eta j))
      else 0) := by
    exact summable_longRatioGradientTail_of_goodFieldOne m zero_le_one hs.2 eta hfield0
  have hB : ∀ j : ℕ,
      BddAbove ((fun x : Vec d =>
        |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |eta i x|) +
          ∏' i : ℕ,
            if m + j ≤ i then Real.exp (4 * |eta i x - eta i 0|) else 1|) ''
        translatedCube d (m + 1 + j) 0) := by
    intro j
    let F : Vec d → ℝ := fun x =>
      |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |eta i x|) +
        ∏' i : ℕ,
          if m + j ≤ i then Real.exp (4 * |eta i x - eta i 0|) else 1|
    let G : Vec d → ℝ := fun x =>
      |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
        ∏' i : ℕ,
          if m + j ≤ i then Real.exp (4 * |omega i x - omega i w|) else 1|
    have hFG : ∀ x : Vec d, F x = G (x + w) := by
      intro x
      simp only [F, G, eta,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.translatePotentialSample_apply,
        zero_add]
    have hset : F '' translatedCube d (m + 1 + j) 0 =
        G '' translatedCube d (m + 1 + j) w := by
      have himage : (fun p : Vec d => w + p) ''
          translatedCube d (m + 1 + j) 0 =
          translatedCube d (m + 1 + j) w := by
        simpa using
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.image_add_left_translatedCube
            w (m + 1 + j) 0)
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : x + w ∈ translatedCube d (m + 1 + j) w := by
          have hx'' : w + x ∈ translatedCube d (m + 1 + j) w := by
            rw [← himage]
            exact ⟨x, hx, rfl⟩
          simpa [add_comm] using hx''
        exact ⟨x + w, hx', (hFG x).symm⟩
      · rintro ⟨x, hx, rfl⟩
        have hx' : x ∈ (fun p : Vec d => w + p) ''
            translatedCube d (m + 1 + j) 0 := by
          rw [himage]
          exact hx
        rcases hx' with ⟨y, hy, rfl⟩
        exact ⟨y, hy, by simpa [add_comm] using hFG y⟩
    rw [show (fun x : Vec d =>
        |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |eta i x|) +
          ∏' i : ℕ,
            if m + j ≤ i then Real.exp (4 * |eta i x - eta i 0|) else 1|) = F by
      rfl, hset]
    exact (hprod j).2.1
  have hsites'' := hsites' M s hs hsmall L m hmL w omega homega
  dsimp [eta] at hsites'' ⊢
  exact ⟨hA, hB, hsites''⟩

end SubdiffusiveProcess.Paper
