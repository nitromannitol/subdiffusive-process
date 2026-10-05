module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHighCutoffEllipticity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.InductionHypothesis
public import SubdiffusiveProcess.Section4.CoarseGrainedBound
public import SubdiffusiveProcess.Section4.EllipticityBound

@[expose] public section

/-!
# Weighted descendant ellipticity at the one-step source scale

This module performs the source-scale specialization of the weighted
descendant maximum in `l.ellipticity.bound`.  It follows the small-exponent
localization route used by Superdiffusion's
`ApproximateRecurrence/LocalizationOscillationBudget.lean`: take a large
fixed moment, aggregate at `s = 1/64`, spend the sharp cardinality root, and
then use the sixteen-logarithm buffer to absorb the remaining scale factor.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

def sourceEllipticityExponent (d : ℕ) : ℝ :=
  1024 * ((d : ℝ) + 1)

def sourceEllipticityWeight : ℝ := 1 / 64

theorem sourceEllipticityExponent_pos (d : ℕ) :
    0 < sourceEllipticityExponent d := by
  unfold sourceEllipticityExponent
  positivity

theorem sourceEllipticityExponent_large (d : ℕ) :
    (1024 : ℝ) ≤ sourceEllipticityExponent d := by
  unfold sourceEllipticityExponent
  have hd0 : (0 : ℝ) ≤ d := by positivity
  nlinarith

theorem sourceEllipticityWeight_pos :
    0 < sourceEllipticityWeight := by
  norm_num [sourceEllipticityWeight]

/-- The proved Section 4 recursion, specialized at a fixed large moment and
the smaller descendant weight, is uniform at the literal source cell. -/
theorem exists_sourceScale_ellipticityMoment_bound {d : ℕ} [NeZero d] :
    ∃ delta0 R : ℝ, 0 < delta0 ∧ 0 < R ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
        ∀ n : ℕ, oneStepLocalizationDepth M.delta ≤ n →
          paperENNRealLpNorm M.P.toMeasure (sourceEllipticityExponent d)
              (ellipticityMomentObservable M n
                (oneStepLocalizationScale n M.delta : ℤ)
                sourceEllipticityWeight) ≤
            ENNReal.ofReal R := by
  obtain ⟨c0, C0, hc0, hC0, hcoarse⟩ :=
    _root_.SubdiffusiveProcess.Section4.coarse_grained_bound (d := d)
  obtain ⟨c1, C1, hc1, hc1one, hC1, hellipticity⟩ :=
    _root_.SubdiffusiveProcess.Section4.ellipticity_bound (d := d)
  let xi := sourceEllipticityExponent d
  let s := sourceEllipticityWeight
  let K : ℝ := 1 + C0 * xi * Real.log (2 + xi) + xi / (c1 * s)
  let D : ℝ := 1 + C0 * xi + K
  let delta0 : ℝ := (2 * D)⁻¹
  let R : ℝ := 3 * C1 * s⁻¹ * Real.sqrt K
  have hxi : 0 < xi := sourceEllipticityExponent_pos d
  have hs : 0 < s := sourceEllipticityWeight_pos
  have hlog : 0 < Real.log (2 + xi) :=
    Real.log_pos (by linarith)
  have hK : 1 < K := by
    dsimp only [K]
    have hfirst : 0 < C0 * xi * Real.log (2 + xi) := by positivity
    have hsecond : 0 < xi / (c1 * s) := by positivity
    linarith
  have hD : 1 < D := by
    dsimp only [D]
    have : 0 < C0 * xi := by positivity
    linarith
  have hdelta0 : 0 < delta0 := by dsimp only [delta0]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨delta0, R, hdelta0, hR, ?_⟩
  intro M hM n hsource
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaOne : M.delta ≤ 1 :=
    M.shellPrefix.delta_le_half.trans (by norm_num)
  have hdeltaD : 2 * D * M.delta ≤ 1 := by
    calc
      2 * D * M.delta ≤ 2 * D * delta0 :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 1 := by
        dsimp only [delta0]
        field_simp [hD.ne']
  have hdeltaK : K * M.delta ^ 2 < 1 := by
    have hKD : K < D := by dsimp only [D]; nlinarith [mul_pos hC0 hxi]
    have hdeltaHalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
    have hKDdelta : K * M.delta < 1 / 2 := by
      have hKdeltaD : K * M.delta < D * M.delta :=
        mul_lt_mul_of_pos_right hKD hdelta
      have hDdelta : D * M.delta ≤ 1 / 2 := by nlinarith
      linarith
    nlinarith
  let delta1 : ℝ := K * M.delta ^ 2
  have hdelta1 : 0 < delta1 := by dsimp only [delta1]; positivity
  have hdelta1lt : delta1 < 1 := hdeltaK
  have hdeltaSq : M.delta ^ 2 ≤ delta1 := by
    dsimp only [delta1]
    nlinarith [sq_nonneg M.delta]
  have hcoarseRange :
      xi ≤ C0⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
    have hlogNonzero : |Real.log M.delta| ≠ 0 := by
      have hlt : M.delta < 1 :=
        M.shellPrefix.delta_le_half.trans_lt (by norm_num)
      exact abs_ne_zero.mpr (ne_of_lt (Real.log_neg hdelta hlt))
    have hproduct : C0 * xi * (M.delta ^ 2 * |Real.log M.delta|) ≤ 1 := by
      have hlogloss := delta_sq_mul_abs_log_le_self hdelta hdeltaOne
      have hCxiD : C0 * xi ≤ D := by
        dsimp only [D]
        linarith [hK]
      have hmul := mul_le_mul_of_nonneg_left hlogloss
        (mul_nonneg hC0.le hxi.le)
      calc
        C0 * xi * (M.delta ^ 2 * |Real.log M.delta|) ≤
            C0 * xi * M.delta := hmul
        _ ≤ D * M.delta :=
          mul_le_mul_of_nonneg_right hCxiD hdelta.le
        _ ≤ 1 := by nlinarith
    rw [show C0⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ =
        (C0 * (M.delta ^ 2) * |Real.log M.delta|)⁻¹ by
      field_simp [hC0.ne', hdelta.ne', hlogNonzero]]
    have hden : 0 < C0 * (M.delta ^ 2) * |Real.log M.delta| := by
      positivity
    rw [show (C0 * (M.delta ^ 2) * |Real.log M.delta|)⁻¹ =
        (C0 * (M.delta ^ 2) * |Real.log M.delta|)⁻¹ * 1 by ring,
      le_inv_mul_iff₀ hden]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hproduct
  have hcoarseBound : ∀ m : ℕ,
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M m (Ch02.cubeDomain (originCube d (m : ℤ)))) ≤
        ENNReal.ofReal delta1 := by
    intro m
    have hm := (hcoarse M xi
      ((by have := sourceEllipticityExponent_large d; linarith) : 1 ≤ xi)
      hcoarseRange m).1
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : 0 ≤ M.delta ^ 2 := sq_nonneg _
    have hcoeff : C0 * xi * Real.log (2 + xi) ≤ K := by
      dsimp only [K]
      have : 0 ≤ xi / (c1 * s) := by positivity
      linarith
    dsimp only [delta1]
    exact mul_le_mul_of_nonneg_right hcoeff hsq
  have hIH : inductionHypothesis M n xi delta1 :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.inductionHypothesis_of_scale_bounds
      M n ((by have := sourceEllipticityExponent_large d; linarith) : 1 ≤ xi)
      hdelta1 hdelta1lt (fun m _hm ↦ hcoarseBound m)
  have hdim : 4 * (d : ℝ) * s⁻¹ ≤ xi := by
    dsimp only [xi, s, sourceEllipticityExponent, sourceEllipticityWeight]
    have hd0 : (0 : ℝ) ≤ d := by positivity
    norm_num
    linarith
  have hxiElliptic : xi ≤ c1 * s * (M.delta ^ 2)⁻¹ * delta1 := by
    have hcs : 0 < c1 * s := mul_pos hc1 hs
    have hsqpos : 0 < M.delta ^ 2 := sq_pos_of_pos hdelta
    rw [show delta1 = K * M.delta ^ 2 by rfl]
    field_simp [hdelta.ne']
    have hKterm : xi < c1 * s * K := by
      dsimp only [K]
      have hcs0 : 0 ≤ c1 * s := hcs.le
      have hrest : 0 ≤ C0 * xi * Real.log (2 + xi) := by positivity
      calc
        xi = c1 * s * (xi / (c1 * s)) := by field_simp
        _ < c1 * s * (1 + C0 * xi * Real.log (2 + xi) +
            xi / (c1 * s)) := by
          gcongr
          linarith
        _ = c1 * s * K := rfl
    nlinarith
  have haggregate := (hellipticity M n xi delta1
      ((by have := sourceEllipticityExponent_large d; linarith) : 6 ≤ xi)
      hdeltaSq hdelta1lt hIH s hs (by norm_num [s, sourceEllipticityWeight])
      hdim hxiElliptic).1 n (oneStepLocalizationScale n M.delta : ℤ)
      (by
        exact_mod_cast (Nat.sub_le n (oneStepLocalizationDepth M.delta))) (by
        exact_mod_cast (Nat.sub_le n (oneStepLocalizationDepth M.delta)))
  refine haggregate.trans (ENNReal.ofReal_le_ofReal ?_)
  have ha0 : 0 ≤ (d : ℝ) / xi + s / 2 := by positivity
  have ha : (d : ℝ) / xi + s / 2 ≤ 1 / 16 := by
    have hdle : (d : ℝ) ≤ (d : ℝ) + 1 := by linarith
    have hden : 0 < (1024 : ℝ) * ((d : ℝ) + 1) := by positivity
    dsimp only [xi, s, sourceEllipticityExponent, sourceEllipticityWeight]
    have hfrac : (d : ℝ) / (1024 * ((d : ℝ) + 1)) ≤ 1 / 1024 := by
      rw [div_le_iff₀ hden]
      nlinarith
    norm_num at hfrac ⊢
    linarith
  have hdepth := delta_mul_rpow_three_oneStepLocalizationDepth_le_three
    hdelta hdeltaOne ha0 ha
  have hsqrt : Real.sqrt delta1 = Real.sqrt K * M.delta := by
    rw [show delta1 = K * M.delta ^ 2 by rfl, Real.sqrt_mul (by positivity : 0 ≤ K),
      Real.sqrt_sq_eq_abs, abs_of_pos hdelta]
  dsimp only [R]
  rw [hsqrt]
  have hC : 0 ≤ C1 * s⁻¹ * Real.sqrt K := by positivity
  calc
    C1 * s⁻¹ * (Real.sqrt K * M.delta) *
          Real.rpow 3 (((d : ℝ) / xi + s / 2) *
            (((n : ℤ) - (oneStepLocalizationScale n M.delta : ℤ) : ℤ) : ℝ)) =
        (C1 * s⁻¹ * Real.sqrt K) *
          (M.delta * Real.rpow 3
            (((d : ℝ) / xi + s / 2) *
              (oneStepLocalizationDepth M.delta : ℝ))) := by
      rw [show ((n : ℤ) - (oneStepLocalizationScale n M.delta : ℤ) : ℤ) =
          (oneStepLocalizationDepth M.delta : ℤ) by
        have hjAdd : oneStepLocalizationScale n M.delta +
            oneStepLocalizationDepth M.delta = n := by
          exact oneStepLocalizationScale_add_depth (by
            simpa [oneStepLocalizationDepth, oneStepSourceLogThreeCeil]
              using hsource)
        have hjAddInt : (oneStepLocalizationScale n M.delta : ℤ) +
            (oneStepLocalizationDepth M.delta : ℤ) = (n : ℤ) := by
          exact_mod_cast hjAdd
        omega]
      push_cast
      ring
    _ ≤ (C1 * s⁻¹ * Real.sqrt K) * 3 :=
      mul_le_mul_of_nonneg_left hdepth hC
    _ = 3 * C1 * s⁻¹ * Real.sqrt K := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
