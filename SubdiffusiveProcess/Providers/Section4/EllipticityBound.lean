import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.EllipticitySpecialization
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.PositiveScaleMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.ResponseLocalization
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SuffixMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitResponse
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.EllipticityAggregation
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpTwoBlockMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitResponseMoment
import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds

/-!
# Ellipticity-bound provider spine

This module contains the sorry-free assembly above the remaining Step 1--2
moment estimate in the paper's proof of `l.ellipticity.bound`.  In particular,
the second conclusion is not an independent seam: it follows from the first
conclusion by the diagonal specialization proved in
`Section4Support.EllipticitySpecialization`.

The exact frozen provider export is intentionally absent until the first-display
estimate is proved.  This module does not import the frozen target.
-/

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace SubdiffusiveProcess.Providers.Section4

open Homogenization Homogenization.Book

/-- Exact assembly of both conclusions of `l.ellipticity.bound` from its
first-display moment estimate.  The hypothesis is the precise remaining
analytic residue, with no altered range or normalization. -/
theorem ellipticity_bound_of_first_display {d : ℕ}
    (c C : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C)
    (hfirst : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (m0 : ℕ) (ξ delta1 : ℝ),
        6 ≤ ξ → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        inductionHypothesis M m0 ξ delta1 →
        ∀ s : ℝ, 0 < s → s ≤ 1 →
          4 * (d : ℝ) * s⁻¹ ≤ ξ →
          ξ ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
          ∀ (m : ℕ) (n : ℤ), n ≤ (m0 : ℤ) → n ≤ (m : ℤ) →
            paperENNRealLpNorm M.P.toMeasure ξ
                (ellipticityMomentObservable M m n s) ≤
              ENNReal.ofReal
                (C * s⁻¹ * Real.sqrt delta1 *
                  Real.rpow 3
                    (((d : ℝ) / ξ + s / 2) * (((m : ℤ) - n : ℤ) : ℝ)))) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (m0 : ℕ) (ξ delta1 : ℝ),
        6 ≤ ξ → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        inductionHypothesis M m0 ξ delta1 →
        ∀ s : ℝ, 0 < s → s ≤ 1 →
          4 * (d : ℝ) * s⁻¹ ≤ ξ →
          ξ ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
          (∀ (m : ℕ) (n : ℤ), n ≤ (m0 : ℤ) → n ≤ (m : ℤ) →
            paperENNRealLpNorm M.P.toMeasure ξ
                (ellipticityMomentObservable M m n s) ≤
              ENNReal.ofReal
                (C * s⁻¹ * Real.sqrt delta1 *
                  Real.rpow 3
                    (((d : ℝ) / ξ + s / 2) * (((m : ℤ) - n : ℤ) : ℝ)))) ∧
          (∀ L : ℕ, L ≤ m0 →
            paperENNRealLpNorm M.P.toMeasure ξ
                (homogenizationErrorRandom M L L s) ≤
              ENNReal.ofReal (C * s⁻¹ * Real.sqrt delta1)) := by
  refine ⟨c, C, hc, hc1, hC, ?_⟩
  intro M m0 ξ delta1 hξ hdelta hdelta1 hIH s hs hs1 hdim hupper
  constructor
  · exact hfirst M m0 ξ delta1 hξ hdelta hdelta1 hIH s hs hs1 hdim hupper
  · intro L hLm0
    have hdiag := hfirst M m0 ξ delta1 hξ hdelta hdelta1 hIH
      s hs hs1 hdim hupper L (L : ℤ) (by exact_mod_cast hLm0) le_rfl
    calc
      paperENNRealLpNorm M.P.toMeasure ξ
          (homogenizationErrorRandom M L L s) ≤
          paperENNRealLpNorm M.P.toMeasure ξ
            (ellipticityMomentObservable M L (L : ℤ) s) :=
        homogenizationErrorRandom_lpnorm_le_ellipticityMomentObservable_self
          M L (by linarith)
      _ ≤ ENNReal.ofReal
          (C * s⁻¹ * Real.sqrt delta1 *
            Real.rpow 3
              (((d : ℝ) / ξ + s / 2) *
                (((L : ℤ) - (L : ℤ) : ℤ) : ℝ))) := hdiag
      _ = ENNReal.ofReal (C * s⁻¹ * Real.sqrt delta1) := by simp

/-- The first display of `l.ellipticity.bound`, obtained by combining the two
P-40 response moments across the normalized geometric depth series. -/
theorem ellipticity_first_display {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (m0 : ℕ) (xi delta1 : ℝ),
        6 ≤ xi → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        inductionHypothesis M m0 xi delta1 →
        ∀ s : ℝ, 0 < s → s ≤ 1 →
          4 * (d : ℝ) * s⁻¹ ≤ xi →
          xi ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
          ∀ (m : ℕ) (n : ℤ), n ≤ (m0 : ℤ) → n ≤ (m : ℤ) →
            paperENNRealLpNorm M.P.toMeasure xi
                (ellipticityMomentObservable M m n s) ≤
              ENNReal.ofReal
                (C * s⁻¹ * Real.sqrt delta1 *
                  Real.rpow 3
                    (((d : ℝ) / xi + s / 2) *
                      (((m : ℤ) - n : ℤ) : ℝ))) := by
  rcases positiveScaleResponseMoment_of_annealed_ordering
      (fun M m k hkm =>
        SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2 M m k hkm) with
    ⟨cPos, CPos, hcPos, hcPos1, hCPos, hpos⟩
  rcases subunit_response_moment (d := d) with
    ⟨cSub, CSub, hcSub, hcSub1, hCSub, hsub⟩
  let c := min cPos cSub
  let K := max CPos CSub
  let C := 20 * K
  have hc : 0 < c := lt_min hcPos hcSub
  have hc1 : c ≤ 1 := (min_le_left _ _).trans hcPos1
  have hK : 1 ≤ K := hCPos.trans (le_max_left _ _)
  have hC : 1 ≤ C := by dsimp only [C]; nlinarith
  refine ⟨c, C, hc, hc1, hC, ?_⟩
  intro M m0 xi delta1 hxi hdelta hdelta1 hIH s hs hs1 hdim hupper m n hnm0 hnm
  have hxiPos : 0 < xi := by linarith
  have hxi1 : 1 ≤ xi := by linarith
  have hdelta0 : 0 ≤ delta1 :=
    (sq_nonneg M.delta).trans hdelta
  have hfactor0 : 0 ≤ s * (M.delta ^ 2)⁻¹ * delta1 := by positivity
  have hupperPos : xi ≤ cPos * s * (M.delta ^ 2)⁻¹ * delta1 :=
    hupper.trans (calc
      c * s * (M.delta ^ 2)⁻¹ * delta1 =
          c * (s * (M.delta ^ 2)⁻¹ * delta1) := by ring
      _ ≤ cPos * (s * (M.delta ^ 2)⁻¹ * delta1) :=
        mul_le_mul_of_nonneg_right (min_le_left cPos cSub) hfactor0
      _ = _ := by ring)
  have hupperSub : xi ≤ cSub * s * (M.delta ^ 2)⁻¹ * delta1 :=
    hupper.trans (calc
      c * s * (M.delta ^ 2)⁻¹ * delta1 =
          c * (s * (M.delta ^ 2)⁻¹ * delta1) := by ring
      _ ≤ cSub * (s * (M.delta ^ 2)⁻¹ * delta1) :=
        mul_le_mul_of_nonneg_right (min_le_right cPos cSub) hfactor0
      _ = _ := by ring)
  let a : ℝ := (d : ℝ) / xi + s / 2
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact add_nonneg (div_nonneg (by positivity) hxiPos.le) (by positivity)
  have hdOver : (d : ℝ) / xi ≤ s / 4 := by
    have hratio : (4 * (d : ℝ) * s⁻¹) / xi ≤ 1 :=
      (div_le_one hxiPos).2 hdim
    calc
      (d : ℝ) / xi = ((4 * (d : ℝ) * s⁻¹) / xi) * (s / 4) := by
        field_simp [hs.ne', hxiPos.ne']
      _ ≤ 1 * (s / 4) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = s / 4 := one_mul _
  have haUpper : a ≤ 3 * s / 4 := by dsimp only [a]; linarith
  have haLt : a < s := lt_of_le_of_lt haUpper (by linarith)
  let N := Int.toNat ((m : ℤ) - n)
  have hNcast : (N : ℝ) = (((m : ℤ) - n : ℤ) : ℝ) := by
    dsimp only [N]
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hnm)
  let Y : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞ :=
    fun l omega => ENNReal.ofReal (Ch02.geometricWeight s 1 l) *
      ellipticityScaleResponseObservable M m n l omega
  have hYmeas : ∀ l, Measurable (Y l) := by
    intro l
    exact (measurable_ellipticityScaleResponseObservable M m n l).const_mul _
  have hpoint := ellipticityMomentObservable_le_scaleSeries M m n s
  have hstart : paperENNRealLpNorm M.P.toMeasure xi
      (ellipticityMomentObservable M m n s) ≤
      ∑' l, paperENNRealLpNorm M.P.toMeasure xi (Y l) := by
    calc
      _ ≤ paperENNRealLpNorm M.P.toMeasure xi (fun omega => ∑' l, Y l omega) :=
        paperENNRealLpNorm_mono_ae M.P.toMeasure hxiPos.le
          (Filter.Eventually.of_forall hpoint)
      _ ≤ _ := paperENNRealLpNorm_tsum_le_tsum M.P.toMeasure hxi1 Y hYmeas
  refine hstart.trans ?_
  have hscale : ∀ l : ℕ,
      paperENNRealLpNorm M.P.toMeasure xi
          (ellipticityScaleResponseObservable M m n l) ≤
        ENNReal.ofReal (K * Real.sqrt delta1 *
          Real.rpow 3 (a * ((N + l : ℕ) : ℝ))) := by
    intro l
    by_cases hkneg : n - (l : ℤ) < 0
    · have hsubMoment := hsub M xi delta1 s m (n - (l : ℤ)) hxi1
        hdelta hdelta1 hs hs1 hdim hupperSub hkneg
      change paperENNRealLpNorm M.P.toMeasure xi
          (subunitResponseObservable M m (n - (l : ℤ))) ≤
        ENNReal.ofReal (CSub * delta1 *
          Real.rpow 3 (s * (m : ℝ))) at hsubMoment
      have hsubK : paperENNRealLpNorm M.P.toMeasure xi
          (subunitResponseObservable M m (n - (l : ℤ))) ≤
          ENNReal.ofReal (K * delta1 * Real.rpow 3 (s * (m : ℝ))) :=
        hsubMoment.trans (ENNReal.ofReal_le_ofReal (by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
          exact mul_le_mul_of_nonneg_right (le_max_right CPos CSub) hdelta0))
      have hbound := ellipticityScaleResponseMoment_le_subunit M m l s xi delta1 K
        hnm hkneg hxiPos hs hdelta0 hK hsubK
      simpa only [a, hNcast, Nat.cast_add] using hbound
    · have hk0 : 0 ≤ n - (l : ℤ) := le_of_not_gt hkneg
      let k := Int.toNat (n - (l : ℤ))
      have hk : (k : ℤ) = n - (l : ℤ) := Int.toNat_of_nonneg hk0
      have hkm : k ≤ m := by
        exact_mod_cast (calc
          (k : ℤ) = n - (l : ℤ) := hk
          _ ≤ n := sub_le_self _ (by exact_mod_cast Nat.zero_le l)
          _ ≤ (m : ℤ) := hnm)
      have hkm0 : k ≤ m0 := by
        exact_mod_cast (calc
          (k : ℤ) = n - (l : ℤ) := hk
          _ ≤ n := sub_le_self _ (by exact_mod_cast Nat.zero_le l)
          _ ≤ (m0 : ℤ) := hnm0)
      have hposK : ∀ Q : Homogenization.TriadicCube d,
          Q ∈ descendantsAtScale (originCube d (m : ℤ)) (k : ℤ) →
          paperENNRealLpNorm M.P.toMeasure xi
              (positiveScaleResponseObservable M m Q) ≤
            ENNReal.ofReal (K * delta1 *
              Real.rpow 3 (s * ((m - k : ℕ) : ℝ))) := by
        intro Q hQ
        have hp := hpos M m0 xi delta1 s m k Q hIH hdelta hdelta1 hs hs1
          hupperPos hkm0 hkm hQ
        change paperENNRealLpNorm M.P.toMeasure xi
            (positiveScaleResponseObservable M m Q) ≤
          ENNReal.ofReal (CPos * delta1 *
            Real.rpow 3 (s * ((m - k : ℕ) : ℝ))) at hp
        exact hp.trans (ENNReal.ofReal_le_ofReal (by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
          exact mul_le_mul_of_nonneg_right (le_max_left CPos CSub) hdelta0))
      have hbound := ellipticityScaleResponseMoment_le_positive M m l k s xi
        delta1 K hnm hk hxiPos hdelta0 hK hposK
      simpa only [a, hNcast, Nat.cast_add] using hbound
  have hterm : ∀ l,
      paperENNRealLpNorm M.P.toMeasure xi (Y l) ≤
        ENNReal.ofReal (Ch02.geometricWeight s 1 l *
          (K * Real.sqrt delta1 *
            Real.rpow 3 (a * ((N + l : ℕ) : ℝ)))) := by
    intro l
    rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure hxiPos _ _
      (measurable_ellipticityScaleResponseObservable M m n l)]
    calc
      _ ≤ ENNReal.ofReal (Ch02.geometricWeight s 1 l) *
          ENNReal.ofReal (K * Real.sqrt delta1 *
            Real.rpow 3 (a * ((N + l : ℕ) : ℝ))) := by
        gcongr
        exact hscale l
      _ = _ := (ENNReal.ofReal_mul
        (Homogenization.geometricWeight_nonneg l (by simpa using hs.le))).symm
  calc
    (∑' l, paperENNRealLpNorm M.P.toMeasure xi (Y l)) ≤
        ∑' l, ENNReal.ofReal (Ch02.geometricWeight s 1 l *
          (K * Real.sqrt delta1 *
            Real.rpow 3 (a * ((N + l : ℕ) : ℝ)))) :=
      ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' l, Ch02.geometricWeight s 1 l *
          (K * Real.sqrt delta1 *
            Real.rpow 3 (a * ((N + l : ℕ) : ℝ)))) := by
      rw [ENNReal.ofReal_tsum_of_nonneg]
      · intro l
        exact mul_nonneg
          (Homogenization.geometricWeight_nonneg l (by simpa using hs.le))
          (mul_nonneg (mul_nonneg (zero_le_one.trans hK)
            (Real.sqrt_nonneg delta1)) (Real.rpow_nonneg (by norm_num) _))
      · exact summable_geometricWeight_mul_shifted_rpow N haLt
    _ ≤ ENNReal.ofReal (20 * K * s⁻¹ * Real.sqrt delta1 *
          Real.rpow 3 (a * (N : ℝ))) :=
      ENNReal.ofReal_le_ofReal (by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          tsum_geometricWeight_mul_shifted_rpow_le N hs hs1
          (mul_nonneg (zero_le_one.trans hK) (Real.sqrt_nonneg delta1))
          ha0 haUpper)
    _ = ENNReal.ofReal (C * s⁻¹ * Real.sqrt delta1 *
          Real.rpow 3 (a * (((m : ℤ) - n : ℤ) : ℝ))) := by
      rw [hNcast]

/-- Exact provider export for the frozen `l.ellipticity.bound` anchor. -/
theorem ellipticity_bound {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (m0 : ℕ) (ξ delta1 : ℝ),
        6 ≤ ξ → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        inductionHypothesis M m0 ξ delta1 →
        ∀ s : ℝ, 0 < s → s ≤ 1 →
          4 * (d : ℝ) * s⁻¹ ≤ ξ →
          ξ ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
          (∀ (m : ℕ) (n : ℤ), n ≤ (m0 : ℤ) → n ≤ (m : ℤ) →
            paperENNRealLpNorm M.P.toMeasure ξ
                (ellipticityMomentObservable M m n s) ≤
              ENNReal.ofReal
                (C * s⁻¹ * Real.sqrt delta1 *
                  Real.rpow 3
                    (((d : ℝ) / ξ + s / 2) * (((m : ℤ) - n : ℤ) : ℝ)))) ∧
          (∀ L : ℕ, L ≤ m0 →
            paperENNRealLpNorm M.P.toMeasure ξ
                (homogenizationErrorRandom M L L s) ≤
              ENNReal.ofReal (C * s⁻¹ * Real.sqrt delta1)) := by
  rcases ellipticity_first_display (d := d) with
    ⟨c, C, hc, hc1, hC, hfirst⟩
  exact ellipticity_bound_of_first_display c C hc hc1 hC hfirst

end SubdiffusiveProcess.Providers.Section4
