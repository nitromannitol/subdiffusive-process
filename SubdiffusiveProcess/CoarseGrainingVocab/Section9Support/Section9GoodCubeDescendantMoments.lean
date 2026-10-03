module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceEllipticityMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHighCutoffEllipticity
@[expose] public section

/-!
# A translated descendant response-moment estimate at the actual outer cutoff.
-/

set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A translated descendant response-moment estimate at the actual outer cutoff. -/
theorem exists_goodCube_descendant_error_moment_constant (d : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (M : GMCModel d) (xi : ℝ),
      6 ≤ xi → 32 * (d : ℝ) ≤ xi →
      xi ≤ K⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
      K * xi * Real.log (2 + xi) * M.delta ^ 2 < 1 →
      ∀ (n m J : ℕ), m ≤ n → n - m ≤ J → ∀ z : Vec d,
        paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
          ellipticityMomentObservable M n (m : ℤ) (1 / 8)
            (translatePotentialSample z omega)) ≤
          ENNReal.ofReal (K * Real.sqrt (K * xi * Real.log (2 + xi) * M.delta ^ 2) *
            Real.rpow 3 ((J : ℝ) / 8)) := by
  obtain ⟨c0, C0, _hc0, hC0, hcoarse⟩ :=
    SubdiffusiveProcess.Frozen.Section4.coarse_grained_bound (d := d)
  obtain ⟨c1, C1, hc1, _hc1one, hC1, hellipticity⟩ :=
    SubdiffusiveProcess.Frozen.Section4.ellipticity_bound (d := d)
  let K : ℝ := max 1 (max C0 (max (16 / c1) (8 * C1)))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hKc0 : C0 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKc1 : 16 / c1 ≤ K :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hKC1 : 8 * C1 ≤ K :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨K, hK1, ?_⟩
  intro M xi hxi6 hxi32 hxiK hsmall n m J hmn hmJ z
  have hxi : 0 < xi := by linarith only [hxi6]
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 + xi) := by
    calc (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
      _ ≤ Real.log (2 + xi) := Real.log_le_log (by norm_num) (by linarith only [hxi])
  have hlog0 : 0 < Real.log (2 + xi) := by linarith only [hlog]
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaSq0 : 0 < M.delta ^ 2 := sq_pos_of_pos hdelta
  let delta1 := K * xi * Real.log (2 + xi) * M.delta ^ 2
  have hdelta1 : 0 < delta1 := by dsimp only [delta1]; positivity
  have hKxi : 6 ≤ K * xi := by
    simpa only [one_mul] using mul_le_mul hK1 hxi6 (by norm_num : (0 : ℝ) ≤ 6) hK0.le
  have hfac1 : 1 ≤ K * xi * Real.log (2 + xi) :=
    (by norm_num : (1 : ℝ) ≤ 6 * (1 / 2)).trans
      (mul_le_mul hKxi hlog (by norm_num) (mul_nonneg hK0.le hxi.le))
  have hdeltaSq : M.delta ^ 2 ≤ delta1 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac1 hdeltaSq0.le
  have hcK : 16 ≤ c1 * K := by
    have h := (div_le_iff₀ hc1).mp hKc1
    simpa only [mul_comm K c1] using h
  have hcK8 : 2 ≤ c1 * (1 / 8 : ℝ) * K := by nlinarith only [hcK]
  have hfac : 1 ≤ c1 * (1 / 8 : ℝ) * K * Real.log (2 + xi) :=
    (by norm_num : (1 : ℝ) ≤ 2 * (1 / 2)).trans
      (mul_le_mul hcK8 hlog (by norm_num) (by positivity))
  have hxiElliptic : xi ≤ c1 * (1 / 8 : ℝ) * (M.delta ^ 2)⁻¹ * delta1 := by
    have hcancel : c1 * (1 / 8 : ℝ) * (M.delta ^ 2)⁻¹ * delta1 =
        xi * (c1 * (1 / 8 : ℝ) * K * Real.log (2 + xi)) := by
      dsimp only [delta1]
      field_simp [hdelta.ne']
    rw [hcancel]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac hxi.le
  have hcoarseRange : xi ≤ C0⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
    apply hxiK.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((inv_le_inv₀ hK0 hC0).mpr hKc0)
        (inv_nonneg.mpr hdeltaSq0.le)) (inv_nonneg.mpr (abs_nonneg _))
  have hcoarseBound : ∀ j : ℕ,
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M j (Ch02.cubeDomain (originCube d (j : ℤ)))) ≤
        ENNReal.ofReal delta1 := by
    intro j
    apply ((hcoarse M xi (by linarith only [hxi6]) hcoarseRange j).1).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKc0 hxi.le) hlog0.le) hdeltaSq0.le
  have hIH := SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.inductionHypothesis_of_scale_bounds
    M n (by linarith only [hxi6]) hdelta1 hsmall (fun j _ => hcoarseBound j)
  have hdim : 4 * (d : ℝ) * ((1 / 8 : ℝ))⁻¹ ≤ xi := by
    norm_num at hxi32 ⊢
    linarith only [hxi32]
  have haggregate := (hellipticity M n xi delta1 hxi6 hdeltaSq hsmall hIH
      (1 / 8 : ℝ) (by norm_num) (by norm_num) hdim hxiElliptic).1
        n (m : ℤ) (by exact_mod_cast hmn) (by exact_mod_cast hmn)
  have hdxi : (d : ℝ) / xi ≤ 1 / 32 := by
    rw [div_le_iff₀ hxi]
    linarith only [hxi32]
  have hdepth : (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) ≤ J := by
    rw [show (n : ℤ) - (m : ℤ) = ((n - m : ℕ) : ℤ) by omega]
    exact_mod_cast hmJ
  have hdepth0 : 0 ≤ (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast (show (0 : ℤ) ≤ (n : ℤ) - (m : ℤ) by omega)
  have hexp : ((d : ℝ) / xi + (1 / 8 : ℝ) / 2) *
      (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) ≤ (J : ℝ) / 8 := by
    calc _ ≤ (1 / 8 : ℝ) * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hdxi]) hdepth0
      _ ≤ (1 / 8 : ℝ) * (J : ℝ) := mul_le_mul_of_nonneg_left hdepth (by norm_num)
      _ = _ := by ring
  rw [paperENNRealLpNorm_comp_translatePotentialSample_eq M z
    (ellipticityMomentObservable M n (m : ℤ) (1 / 8))
    (measurable_ellipticityMomentObservable M n (m : ℤ) (1 / 8))]
  apply haggregate.trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg delta1)
    simpa only [show ((1 / 8 : ℝ))⁻¹ = 8 by norm_num, mul_comm C1 8] using hKC1
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  · exact Real.rpow_nonneg (by norm_num) _
  · exact mul_nonneg hK0.le (Real.sqrt_nonneg delta1)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
