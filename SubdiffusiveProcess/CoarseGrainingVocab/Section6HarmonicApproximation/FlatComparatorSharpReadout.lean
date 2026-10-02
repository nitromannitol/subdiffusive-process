import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorBudgetReadout

/-!
# Sharp additive-dual readout for the flat comparator

The paper's negative fractional dual is defined with the additive test norm
`s^(1/2) [h]_{W^{s,2}} + ‖h‖₂`.  Passing through the power-form completed
`W^{s,2}` norm loses an unnecessary factor `s⁻¹/²`.  This file instead runs
the smooth-density argument directly in the additive norm and therefore
keeps the spectral readout dimension-only on the manuscript corridor.

PROVENANCE: this is the sharp version of the negative-norm readout in
`Algsuperdiff/Section4/Provider/ExcessDecay/NegNormToL2.lean`; the density
argument mirrors CoarseGraining's
`EuclideanWspSmoothDualFieldPairing.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal

noncomputable section

private theorem cubeEuclideanWspKernel_sub
    {d : ℕ} (s : FractionalOrder) (p : FiniteLpExponent)
    (F G : Vec d → Vec d) :
    cubeEuclideanWspKernel s p (fun x ↦ F x - G x) =
      fun z ↦ cubeEuclideanWspKernel s p F z -
        cubeEuclideanWspKernel s p G z := by
  funext z
  rw [cubeEuclideanWspKernel_apply, cubeEuclideanWspKernel_apply,
    cubeEuclideanWspKernel_apply]
  change _ • (HilbertVec.ofVecL d)
    ((F z.1 - G z.1) - (F z.2 - G z.2)) = _
  rw [sub_sub_sub_comm, (HilbertVec.ofVecL d).map_sub, smul_sub]
  rfl

private noncomputable def wspFieldSub
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    (F G : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    CubeEuclideanWspField Q s FiniteLpExponent.two where
  toField := fun x ↦ F.toField x - G.toField x
  euclideanMemLp := by
    simpa only [HilbertVec.ofVecL_apply] using
      F.euclideanMemLp.sub G.euclideanMemLp
  euclideanMemWsp := by
    change MemLp (cubeEuclideanWspKernel s FiniteLpExponent.two
      (fun x ↦ F.toField x - G.toField x)) 2
      (Gagliardo.gagliardoCubeMeasure Q)
    rw [cubeEuclideanWspKernel_sub]
    simpa only [Pi.sub_apply] using
      F.euclideanMemWsp.sub G.euclideanMemWsp

private theorem paperFractionalFullNorm_add_le
    {d : ℕ} {Q : TriadicCube d} (s : FractionalOrder)
    (F G : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    paperFractionalFullNorm Q s FiniteLpExponent.two
        (fun x ↦ F.toField x + G.toField x) ≤
      paperFractionalFullNorm Q s FiniteLpExponent.two F.toField +
        paperFractionalFullNorm Q s FiniteLpExponent.two G.toField := by
  have hkernel : cubeEuclideanWspKernel s FiniteLpExponent.two
        (fun x ↦ F.toField x + G.toField x) =
      fun z ↦ cubeEuclideanWspKernel s FiniteLpExponent.two F.toField z +
        cubeEuclideanWspKernel s FiniteLpExponent.two G.toField z := by
    funext z
    rw [cubeEuclideanWspKernel_apply, cubeEuclideanWspKernel_apply,
      cubeEuclideanWspKernel_apply]
    rw [add_sub_add_comm]
    change _ • (HilbertVec.ofVecL d)
        ((F.toField z.1 - F.toField z.2) +
          (G.toField z.1 - G.toField z.2)) = _
    rw [(HilbertVec.ofVecL d).map_add, smul_add]
    rfl
  have hsemi : cubeEuclideanWspESeminorm Q s FiniteLpExponent.two
        (fun x ↦ F.toField x + G.toField x) ≤
      cubeEuclideanWspESeminorm Q s FiniteLpExponent.two F.toField +
        cubeEuclideanWspESeminorm Q s FiniteLpExponent.two G.toField := by
    unfold cubeEuclideanWspESeminorm
    rw [hkernel]
    exact eLpNorm_add_le F.kernel_aestronglyMeasurable
      G.kernel_aestronglyMeasurable (by norm_num)
  have hlp : (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞) (fun x ↦ F.toField x + G.toField x) ≤
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) F.toField +
        (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) G.toField := by
    unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
      BoundedMeasurableDomain.normalizedLpENorm
    rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    have hpoint : ∀ x, |euclideanNorm (F.toField x + G.toField x)| ≤
        euclideanNorm (F.toField x) + euclideanNorm (G.toField x) := by
      intro x
      rw [abs_of_nonneg (euclideanNorm_nonneg _)]
      simpa only [euclideanNorm_eq_norm_ofVec, ← HilbertVec.ofVecL_apply] using
        norm_add_le (HilbertVec.ofVec (F.toField x))
          (HilbertVec.ofVec (G.toField x))
    calc
      eLpNorm (fun x ↦ euclideanNorm (F.toField x + G.toField x)) 2
          (normalizedCubeMeasure Q) ≤
        eLpNorm (fun x ↦ euclideanNorm (F.toField x) +
          euclideanNorm (G.toField x)) 2
          (normalizedCubeMeasure Q) := by
            exact eLpNorm_mono_real hpoint
      _ ≤ eLpNorm (fun x ↦ euclideanNorm (F.toField x)) 2
            (normalizedCubeMeasure Q) +
          eLpNorm (fun x ↦ euclideanNorm (G.toField x)) 2
            (normalizedCubeMeasure Q) := by
              apply eLpNorm_add_le
              · simpa [euclideanNorm_eq_norm_ofVec] using
                  F.euclideanMemLp.norm.aestronglyMeasurable
              · simpa [euclideanNorm_eq_norm_ofVec] using
                  G.euclideanMemLp.norm.aestronglyMeasurable
              · norm_num
  unfold paperFractionalFullNorm paperFractionalSeminorm
  have hc : 0 ≤ (ENNReal.ofReal s.1) ^
      (FiniteLpExponent.two.exponent.toReal)⁻¹ := by positivity
  have hw : 0 ≤ (ENNReal.ofReal (cubeScaleFactor Q)) ^ (-s.1) := by positivity
  calc
    (ENNReal.ofReal s.1) ^ (FiniteLpExponent.two.exponent.toReal)⁻¹ *
          cubeEuclideanWspESeminorm Q s FiniteLpExponent.two
            (fun x ↦ F.toField x + G.toField x) +
        (ENNReal.ofReal (cubeScaleFactor Q)) ^ (-s.1) *
          (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm 2
            (fun x ↦ F.toField x + G.toField x) ≤
      (ENNReal.ofReal s.1) ^ (FiniteLpExponent.two.exponent.toReal)⁻¹ *
          (cubeEuclideanWspESeminorm Q s FiniteLpExponent.two F.toField +
            cubeEuclideanWspESeminorm Q s FiniteLpExponent.two G.toField) +
        (ENNReal.ofReal (cubeScaleFactor Q)) ^ (-s.1) *
          ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm 2 F.toField +
            (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm 2 G.toField) :=
      add_le_add (by gcongr) (by gcongr)
    _ = _ := by
      simp only [FiniteLpExponent.two_exponent]
      ring

private theorem paperFractionalFullNorm_smooth_le_field_add_error
    {d : ℕ} {Q : TriadicCube d} (s : FractionalOrder)
    (G : CubeEuclideanWspL2Field Q s FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s FiniteLpExponent.two) :
    paperFractionalFullNorm Q s FiniteLpExponent.two h.toField ≤
      paperFractionalFullNorm Q s FiniteLpExponent.two G.toField +
        2 * cubeEuclideanWspFullENorm Q s FiniteLpExponent.two
          (fun x ↦ h.toField x - G.toField x) := by
  let H := h.toCubeEuclideanWspField
  let E := wspFieldSub H G.toCubeEuclideanWspField
  have hsum : (fun x ↦ G.toField x + E.toField x) = h.toField := by
    funext x
    simp [E, H, wspFieldSub]
  have hadd := paperFractionalFullNorm_add_le s G.toCubeEuclideanWspField E
  rw [hsum] at hadd
  have herr := paperFractionalFullNorm_le_two_mul_cubeEuclideanWspFullENorm
    Q s FiniteLpExponent.two E.toField
  have heq : E.toField = fun x ↦ h.toField x - G.toField x := rfl
  rw [heq] at herr
  exact hadd.trans (add_le_add_right herr _)

private theorem fieldPairing_eq_zero_of_paperFullNorm_eq_zero
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (G : CubeEuclideanWspL2Field Q s FiniteLpExponent.two)
    (hG : paperFractionalFullNorm Q s FiniteLpExponent.two G.toField = 0) :
    cubeEuclideanNormalizedFieldPairing F G = 0 := by
  have hfull : cubeEuclideanWspFullENorm Q s FiniteLpExponent.two G.toField = 0 := by
    have h := cubeEuclideanWspFullENorm_le_paperFractionalFullNorm
      Q s FiniteLpExponent.two G.toField
    rw [hG, mul_zero] at h
    exact nonpos_iff_eq_zero.mp h
  have hlp : (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
      (2 : ℝ≥0∞) G.toField = 0 := by
    unfold cubeEuclideanWspFullENorm at hfull
    let W := cubeEuclideanWspScalePowerWeight Q s FiniteLpExponent.two
    let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
      (2 : ℝ≥0∞) G.toField
    let S := cubeEuclideanWspESeminorm Q s FiniteLpExponent.two G.toField
    have hbase : W * L ^ (2 : ℝ) + S ^ (2 : ℝ) = 0 := by
      apply (ENNReal.rpow_eq_zero_iff_of_pos
        (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)).mp
      simpa only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
        using hfull
    have hW : W ≠ 0 := by
      dsimp only [W, cubeEuclideanWspScalePowerWeight]
      exact ne_of_gt (ENNReal.rpow_pos
        (ENNReal.ofReal_pos.mpr (cubeScaleFactor_pos' Q)) ENNReal.ofReal_ne_top)
    have hpow : L ^ (2 : ℝ) = 0 :=
      (mul_eq_zero.mp (add_eq_zero.mp hbase).1).resolve_left hW
    exact (ENNReal.rpow_eq_zero_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mp hpow
  have hlp' : eLpNorm (fun x ↦ HilbertVec.ofVec (G.toField x)) 2
      (normalizedCubeMeasure Q) = 0 := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      euclideanNorm_eq_norm_ofVec, eLpNorm_norm] using hlp
  have hzero : (fun x ↦ HilbertVec.ofVec (G.toField x)) =ᵐ[
      normalizedCubeMeasure Q] 0 :=
    (eLpNorm_eq_zero_iff G.euclideanMemL2.aestronglyMeasurable (by norm_num)).mp hlp'
  unfold cubeEuclideanNormalizedFieldPairing
  apply integral_eq_zero_of_ae
  filter_upwards [hzero] with x hx
  have hx' : G.toField x = 0 := by
    have h := congrArg (HilbertVec.continuousLinearEquivVec d) hx
    simpa only [HilbertVec.continuousLinearEquivVec_apply] using h
  rw [hx']
  exact vecDot_zero_right _



theorem ofReal_abs_normalizedFieldPairing_le_paperDual_mul_paperFullNorm
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (G : CubeEuclideanWspL2Field Q s FiniteLpExponent.two) :
    ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G| ≤
      paperNegativeFractionalDual Q s FiniteLpExponent.two F *
        paperFractionalFullNorm Q s FiniteLpExponent.two G.toField := by
  let D := paperNegativeFractionalDual Q s FiniteLpExponent.two F
  let N := paperFractionalFullNorm Q s FiniteLpExponent.two G.toField
  change ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G| ≤ D * N
  by_cases hD : D < ∞
  · have hfullG : cubeEuclideanWspFullENorm Q s FiniteLpExponent.two
        G.toField < ∞ := G.toCubeEuclideanWspField.fullENorm_lt_top
    have hN : N < ∞ :=
      (paperFractionalFullNorm_le_two_mul_cubeEuclideanWspFullENorm
        Q s FiniteLpExponent.two G.toField).trans_lt
          (ENNReal.mul_lt_top (by norm_num) hfullG)
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top hD.ne hN.ne)).mp
    rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul]
    let A := (eLpNorm (fun x ↦ HilbertVec.ofVec (F.toField x)) 2
      (normalizedCubeMeasure Q)).toReal
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    let delta := epsilon / (2 * D.toReal + A + 1)
    have hdenom : 0 < 2 * D.toReal + A + 1 := by positivity
    have hdelta : 0 < delta := div_pos hepsilon hdenom
    obtain ⟨h, hfull, hl2⟩ :=
      exists_cubeEuclideanWspSmoothTest_fullENorm_and_l2_sub_lt G
        (epsilon := ENNReal.ofReal delta) (ENNReal.ofReal_pos.mpr hdelta)
    have hfullTop : cubeEuclideanWspFullENorm Q s FiniteLpExponent.two
        (fun x ↦ h.toField x - G.toField x) < ∞ :=
      hfull.trans (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
    have hfullReal : (cubeEuclideanWspFullENorm Q s FiniteLpExponent.two
        (fun x ↦ h.toField x - G.toField x)).toReal < delta := by
      have hx := (ENNReal.toReal_lt_toReal hfullTop.ne ENNReal.ofReal_ne_top).mpr hfull
      simpa only [ENNReal.toReal_ofReal hdelta.le] using hx
    have hl2Top : eLpNorm (fun x ↦ HilbertVec.ofVec (h.toField x - G.toField x)) 2
        (normalizedCubeMeasure Q) < ∞ :=
      hl2.trans (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
    have hl2Real : (eLpNorm (fun x ↦ HilbertVec.ofVec
        (h.toField x - G.toField x)) 2 (normalizedCubeMeasure Q)).toReal < delta := by
      have hx := (ENNReal.toReal_lt_toReal hl2Top.ne ENNReal.ofReal_ne_top).mpr hl2
      simpa only [ENNReal.toReal_ofReal hdelta.le] using hx
    have hnorm := paperFractionalFullNorm_smooth_le_field_add_error s G h
    have hnormTop : paperFractionalFullNorm Q s FiniteLpExponent.two h.toField < ∞ :=
      paperFractionalFullNorm_lt_top_of_smooth h
    have hnormReal : (paperFractionalFullNorm Q s FiniteLpExponent.two
        h.toField).toReal ≤ N.toReal + 2 * delta := by
      have herrTop : 2 * cubeEuclideanWspFullENorm Q s FiniteLpExponent.two
          (fun x ↦ h.toField x - G.toField x) ≠ ∞ :=
        (ENNReal.mul_lt_top (by norm_num) hfullTop).ne
      have hx := (ENNReal.toReal_le_toReal hnormTop.ne
        (ENNReal.add_ne_top.mpr ⟨hN.ne, herrTop⟩)).mpr hnorm
      rw [ENNReal.toReal_add hN.ne herrTop, ENNReal.toReal_mul] at hx
      norm_num at hx
      have herrReal : 2 * (cubeEuclideanWspFullENorm Q s FiniteLpExponent.two
          (fun x ↦ h.toField x - G.toField x)).toReal ≤ 2 * delta :=
        mul_le_mul_of_nonneg_left hfullReal.le (by norm_num)
      exact hx.trans (add_le_add_right herrReal _)
    let hc : CubeEuclideanWspSmoothTest Q s FiniteLpExponent.two.conjugate :=
      { toField := h.toField
        contDiff := h.contDiff }
    have hsmoothE :=
      Section6Dirichlet.ofReal_abs_normalizedSmoothPairing_le_paperNegativeFractionalDual_mul_fullNorm
        (p := FiniteLpExponent.two) F hc
    have hsmoothE' : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
        D * paperFractionalFullNorm Q s FiniteLpExponent.two h.toField := by
      simpa only [hc, FiniteLpExponent.conjugate_two, D] using hsmoothE
    have hsmooth : |cubeEuclideanNormalizedSmoothPairing F h| ≤
        D.toReal * (paperFractionalFullNorm Q s FiniteLpExponent.two h.toField).toReal := by
      have hx := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hD.ne hnormTop.ne)).mpr hsmoothE'
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul] using hx
    have hFmem : ∀ i : Fin d, MemLp (fun x ↦ F.toField x i) 2
        (normalizedCubeMeasure Q) := by
      intro i
      simpa only [FiniteLpExponent.two_exponent, HilbertVec.ofVec,
        PiLp.toLp_apply] using F.euclideanMemLp.eval_piLp i
    have hGmem : ∀ i : Fin d, MemLp (fun x ↦ G.toField x i) 2
        (normalizedCubeMeasure Q) := by
      intro i
      simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using G.euclideanMemL2.eval_piLp i
    have hhmem : ∀ i : Fin d, MemLp (fun x ↦ h.toField x i) 2
        (normalizedCubeMeasure Q) := by
      intro i
      simpa only [FiniteLpExponent.two_exponent, HilbertVec.ofVec,
        PiLp.toLp_apply] using h.euclideanMemLp_two.eval_piLp i
    have hpairDiff : cubeEuclideanNormalizedFieldPairing F G -
          cubeEuclideanNormalizedSmoothPairing F h =
        ∫ x, vecDot (F.toField x) (G.toField x - h.toField x)
          ∂normalizedCubeMeasure Q := by
      unfold cubeEuclideanNormalizedFieldPairing cubeEuclideanNormalizedSmoothPairing
      rw [← integral_sub
        (by simpa only [vecDot] using
          (integrable_finset_sum Finset.univ
            (fun i _ ↦ (hFmem i).integrable_mul (hGmem i))))
        (by simpa only [vecDot] using
          (integrable_finset_sum Finset.univ
            (fun i _ ↦ (hFmem i).integrable_mul (hhmem i))))]
      apply integral_congr_ae
      filter_upwards with x
      simp only [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
    have hl2Eq : eLpNorm (fun x ↦ HilbertVec.ofVec (G.toField x - h.toField x)) 2
          (normalizedCubeMeasure Q) =
        eLpNorm (fun x ↦ HilbertVec.ofVec (h.toField x - G.toField x)) 2
          (normalizedCubeMeasure Q) := by
      have hfun : (fun x ↦ HilbertVec.ofVec (G.toField x - h.toField x)) =
          -(fun x ↦ HilbertVec.ofVec (h.toField x - G.toField x)) := by
        funext x
        rw [Pi.neg_apply, show G.toField x - h.toField x =
          -(h.toField x - G.toField x) by abel, ← HilbertVec.ofVecL_apply]
        exact (HilbertVec.ofVecL d).map_neg _
      rw [hfun, eLpNorm_neg]
    have hdifference : |cubeEuclideanNormalizedFieldPairing F G -
        cubeEuclideanNormalizedSmoothPairing F h| ≤
        A * (eLpNorm (fun x ↦ HilbertVec.ofVec (h.toField x - G.toField x)) 2
          (normalizedCubeMeasure Q)).toReal := by
      rw [hpairDiff, ← hl2Eq]
      exact CubeCalderonZygmund.INTERNAL.abs_integral_vecDot_le_eLpNorm_toReal_mul
        (by simpa only [FiniteLpExponent.two_exponent] using F.euclideanMemLp)
        (by simpa only [HilbertVec.ofVecL_apply, sub_eq_add_neg, add_comm] using
          G.euclideanMemL2.sub h.euclideanMemLp_two)
    calc
      |cubeEuclideanNormalizedFieldPairing F G| ≤
          |cubeEuclideanNormalizedSmoothPairing F h| +
            |cubeEuclideanNormalizedFieldPairing F G -
              cubeEuclideanNormalizedSmoothPairing F h| := by
        calc
          _ = |cubeEuclideanNormalizedSmoothPairing F h +
              (cubeEuclideanNormalizedFieldPairing F G -
                cubeEuclideanNormalizedSmoothPairing F h)| := by
                  congr 1
                  ring
          _ ≤ _ := abs_add_le _ _
      _ ≤ D.toReal * (paperFractionalFullNorm Q s FiniteLpExponent.two
            h.toField).toReal +
          A * (eLpNorm (fun x ↦ HilbertVec.ofVec (h.toField x - G.toField x)) 2
            (normalizedCubeMeasure Q)).toReal := add_le_add hsmooth hdifference
      _ ≤ D.toReal * (N.toReal + 2 * delta) + A * delta := by gcongr
      _ = D.toReal * N.toReal + (2 * D.toReal + A) * delta := by ring
      _ ≤ D.toReal * N.toReal + epsilon := by
        gcongr
        rw [show (2 * D.toReal + A) * delta =
          epsilon * (2 * D.toReal + A) / (2 * D.toReal + A + 1) by
            dsimp only [delta]
            ring]
        apply (div_le_iff₀ hdenom).mpr
        exact mul_le_mul_of_nonneg_left (by linarith) hepsilon.le
  · have hDtop : D = ∞ := ((not_lt.mp hD).antisymm le_top).symm
    by_cases hNzero : N = 0
    · rw [hDtop, hNzero]
      rw [fieldPairing_eq_zero_of_paperFullNorm_eq_zero F G hNzero]
      simp
    · rw [hDtop, ENNReal.top_mul hNzero]
      exact le_top

/-- The divergence lift's additive manuscript norm has a dimension-only
bound throughout the harmonic-approximation order corridor. -/
theorem paperFractionalFullNorm_unitCubeVectorH1_le_uniform
    {d : ℕ} [NeZero d] (s : FractionalOrder) (hs : s.1 ≤ 1 / 4)
    (V : CubeVectorH1Function (originCube d 0)) :
    paperFractionalFullNorm (originCube d 0) s FiniteLpExponent.two V.toField ≤
      ((allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 + 1) *
        Section6Dirichlet.unitCubeVectorH1ENormBudget V := by
  have hsemi : paperFractionalSeminorm (originCube d 0) s
      FiniteLpExponent.two V.toField ≤
      Section6Dirichlet.scaledVectorDatumFractionalConstant s d *
        Section6Dirichlet.unitCubeVectorH1ENormBudget V := by
    have hfield : (Section6Dirichlet.centeredCubeScaledVectorDilation
        (1 : ℝ) 0 V).toField =
        V.toField := by
      funext x
      rw [Section6Dirichlet.centeredCubeScaledVectorDilation_toField]
      simp
    rw [← hfield]
    simpa [Section6Dirichlet.scaledVectorDatumFractionalENormBound] using
      Section6Dirichlet.paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_h1Budget
        (1 : ℝ) 0 s V
  have hL2 : (cubeBoundedMeasurableDomain (originCube d 0)).normalizedEuclideanLpENorm
      (2 : ℝ≥0∞) V.toField ≤ Section6Dirichlet.unitCubeVectorH1ENormBudget V := by
    unfold Section6Dirichlet.unitCubeVectorH1ENormBudget
    exact le_add_right le_rfl
  rw [paperFractionalFullNorm]
  simp only [cubeScaleFactor_originCube, zpow_zero, ENNReal.ofReal_one,
    ENNReal.one_rpow, one_mul]
  calc
    _ ≤ Section6Dirichlet.scaledVectorDatumFractionalConstant s d *
          Section6Dirichlet.unitCubeVectorH1ENormBudget V +
        Section6Dirichlet.unitCubeVectorH1ENormBudget V := add_le_add hsemi hL2
    _ = (Section6Dirichlet.scaledVectorDatumFractionalConstant s d + 1) *
        Section6Dirichlet.unitCubeVectorH1ENormBudget V := by ring
    _ ≤ ((allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 + 1) *
        Section6Dirichlet.unitCubeVectorH1ENormBudget V := by
      gcongr
      exact scaledVectorDatumFractionalConstant_le (d := d) s hs

/-! ## Dimension-only zero-trace readout -/

/-- The dimension-only constant in the sharp additive-dual spectral
readout. -/
noncomputable def flatComparatorSharpSpectralConstant
    (d : ℕ) [NeZero d] : ℝ≥0∞ :=
  ((allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 + 1) *
    ENNReal.ofReal (Section6Dirichlet.unitDivergenceLiftConstant d)

theorem flatComparatorSharpSpectralConstant_lt_top
    (d : ℕ) [NeZero d] : flatComparatorSharpSpectralConstant d < ∞ := by
  unfold flatComparatorSharpSpectralConstant
  apply ENNReal.mul_lt_top
  · apply ENNReal.add_lt_top.2
    exact ⟨ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (allDimensionalHsToSampleConstant_lt_top d).ne) (by norm_num),
      ENNReal.one_lt_top⟩
  · exact ENNReal.ofReal_lt_top

/-- The unit-cube zero-trace `L²` readout directly in the additive paper
dual.  Its coefficient is independent of the fractional order on
`0 < s ≤ 1/4`. -/
theorem l2Size_le_paperNegativeFractionalDual_gradient_uniform
    {d : ℕ} [NeZero d] (s : FractionalOrder) (hs : s.1 ≤ 1 / 4)
    (w : H10Function (openCubeSet (originCube d 0))) :
    l2Size (originCube d 0) w.toH1Function.toFun ≤
      flatComparatorSharpSpectralConstant d *
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (Section6Dirichlet.unitH10GradientEuclideanL2Field w) := by
  let L : ℝ≥0∞ := l2Size (originCube d 0) w.toH1Function.toFun
  let D : ℝ≥0∞ := paperNegativeFractionalDual (originCube d 0) s
    FiniteLpExponent.two (Section6Dirichlet.unitH10GradientEuclideanL2Field w)
  obtain ⟨V, hV, hbudget⟩ :=
    (Section6Dirichlet.exists_unitCubeVectorH1Function_divergence_lift_h1ENormBudget
      d).choose_spec.2 w.toH1Function.toFun w.toH1Function.memL2
  let G := Section6Dirichlet.unitCubeVectorH1WspL2Field s V
  have hpairBound :
      ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing
          (Section6Dirichlet.unitH10GradientEuclideanL2Field w) G| ≤
        D * paperFractionalFullNorm (originCube d 0) s
          FiniteLpExponent.two G.toField := by
    simpa only [D] using
      (ofReal_abs_normalizedFieldPairing_le_paperDual_mul_paperFullNorm
        (Section6Dirichlet.unitH10GradientEuclideanL2Field w) G)
  have hpairReal : cubeEuclideanNormalizedFieldPairing
      (Section6Dirichlet.unitH10GradientEuclideanL2Field w) G =
      -(∫ x in openCubeSet (originCube d 0),
          w.toH1Function.toFun x ^ 2 ∂volume) := by
    have hw := hV w
    unfold cubeEuclideanNormalizedFieldPairing
    rw [normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
    calc
      (∫ x in openCubeSet (originCube d 0),
          vecDot ((Section6Dirichlet.unitH10GradientEuclideanL2Field w).toField x)
            (G.toField x) ∂volume) =
        ∫ x in openCubeSet (originCube d 0),
          vecDot (V.toField x) (w.toH1Function.grad x) ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Section6Dirichlet.unitH10GradientEuclideanL2Field_toField,
              Section6Dirichlet.unitCubeVectorH1WspL2Field_toField]
            exact vecDot_comm _ _
      _ = -(∫ x in openCubeSet (originCube d 0),
          w.toH1Function.toFun x ^ 2 ∂volume) := by
        have hw' : (∫ x in openCubeSet (originCube d 0),
            w.toH1Function.toFun x ^ 2 ∂volume) =
            -(∫ x in openCubeSet (originCube d 0),
              vecDot (V.toField x) (w.toH1Function.grad x) ∂volume) := by
          simpa only [pow_two] using hw
        linarith
  have hIntegralNonneg : 0 ≤ ∫ x in openCubeSet (originCube d 0),
      w.toH1Function.toFun x ^ 2 ∂volume :=
    integral_nonneg fun x ↦ sq_nonneg _
  have hLtop : L ≠ ∞ := w.toH1Function.memL2.eLpNorm_ne_top
  have hLnorm : L = ENNReal.ofReal ‖toScalarL2 w.toH1Function.memL2‖ := by
    unfold L l2Size
    exact (Lp.enorm_toLp w.toH1Function.memL2).symm.trans
      (ofReal_norm_eq_enorm (toScalarL2 w.toH1Function.memL2)).symm
  have hLsq : L ^ 2 = ENNReal.ofReal
      (∫ x in openCubeSet (originCube d 0),
        w.toH1Function.toFun x ^ 2 ∂volume) := by
    have hreal := toReal_eLpNorm_two_sq_eq_integral_sq w.toH1Function.memL2
    rw [← hreal]
    unfold L l2Size at hLtop ⊢
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hLtop]
  have hpairL : L ^ 2 ≤ D *
      paperFractionalFullNorm (originCube d 0) s FiniteLpExponent.two G.toField := by
    rw [hLsq, ← abs_of_nonneg hIntegralNonneg, ← abs_neg, ← hpairReal]
    exact hpairBound
  have hfull := paperFractionalFullNorm_unitCubeVectorH1_le_uniform s hs V
  rw [Section6Dirichlet.unitCubeVectorH1WspL2Field_toField] at hpairL
  have hbudget' : Section6Dirichlet.unitCubeVectorH1ENormBudget V ≤
      ENNReal.ofReal (Section6Dirichlet.unitDivergenceLiftConstant d *
        ‖toScalarL2 w.toH1Function.memL2‖) := by
    simpa [Section6Dirichlet.unitDivergenceLiftConstant] using hbudget
  have hmain : L * L ≤ flatComparatorSharpSpectralConstant d * D * L := by
    calc
      L * L ≤ D * paperFractionalFullNorm (originCube d 0) s
          FiniteLpExponent.two V.toField := by simpa only [pow_two] using hpairL
      _ ≤ D * (((allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 + 1) *
          Section6Dirichlet.unitCubeVectorH1ENormBudget V) :=
        by simpa only [mul_comm] using mul_le_mul_right hfull D
      _ ≤ D * (((allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 + 1) *
          ENNReal.ofReal (Section6Dirichlet.unitDivergenceLiftConstant d *
            ‖toScalarL2 w.toH1Function.memL2‖)) := by
        have hi := mul_le_mul_right hbudget'
          ((allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) * 9 + 1)
        have ho := mul_le_mul_right hi D
        simpa only [mul_comm, mul_left_comm, mul_assoc] using ho
      _ = flatComparatorSharpSpectralConstant d * D * L := by
        rw [ENNReal.ofReal_mul
          (Section6Dirichlet.unitDivergenceLiftConstant_nonneg d), ← hLnorm]
        unfold flatComparatorSharpSpectralConstant
        ring
  by_cases hL0 : L = 0
  · simp [L, hL0]
  · change L ≤ flatComparatorSharpSpectralConstant d * D
    calc
      L = L⁻¹ * (L * L) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hL0 hLtop, one_mul]
      _ ≤ L⁻¹ * (flatComparatorSharpSpectralConstant d * D * L) :=
        mul_le_mul_right hmain L⁻¹
      _ = flatComparatorSharpSpectralConstant d * D := by
        calc
          L⁻¹ * (flatComparatorSharpSpectralConstant d * D * L) =
              (flatComparatorSharpSpectralConstant d * D) * (L⁻¹ * L) := by ring
          _ = _ := by rw [ENNReal.inv_mul_cancel hL0 hLtop, mul_one]

/-! ## Physical-cube transport -/

/-- Sharp physical-cube version of the scalar coarse-graining readout.  The
constant is dimension-only; the hypothesis `s ≤ 1/4` is exactly the
manuscript corridor used by harmonic approximation. -/
theorem cubeLpNorm_sub_le_sharpSpectral_of_physicalCoarseGraining
    {d : ℕ} [NeZero d] (m : ℤ) {alpha : ℝ} (halpha : 0 < alpha)
    (s : FractionalOrder) (hs : s.1 ≤ 1 / 4)
    (u v : H1Function (openCubeSet (originCube d m)))
    (hzero : HasH10Difference (originCube d m) u v)
    (Fflux : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two)
    {B : ℝ}
    (hphysical :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            ENNReal.ofReal alpha *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeGradientDifferenceL2Field m u v) +
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two Fflux ≤
        ENNReal.ofReal B) :
    cubeLpNorm (originCube d m) 2 (fun x => u.toFun x - v.toFun x) ≤
      (flatComparatorSharpSpectralConstant d *
        ENNReal.ofReal (centeredCubeScale m * alpha⁻¹ * B)).toReal := by
  obtain ⟨w, hw⟩ := hzero
  let R : ℝ := centeredCubeScale m
  let uv : H1Function (openCubeSet (originCube d m)) := u - v
  let wUnit : H10Function (openCubeSet (originCube d 0)) :=
    R • centeredCubeNormalizedPullback w
  let Fgrad := centeredCubeGradientDifferenceL2Field m u v
  let FgradUnit := scaledCenteredCubePullbackEuclideanL2Field m R Fgrad
  have hdualSum := unitPaperNegativeDualSum_le_of_physicalCoarseGraining
    m halpha s Fgrad Fflux hphysical
  have hdualGrad :
      paperNegativeFractionalDual (originCube d 0) s
          FiniteLpExponent.two FgradUnit ≤
        ENNReal.ofReal (R * alpha⁻¹ * B) := by
    exact le_trans (le_add_right le_rfl)
      (by simpa only [R, Fgrad, FgradUnit] using hdualSum)
  have hwgrad :
      (Section6Dirichlet.unitH10GradientEuclideanL2Field wUnit).toField =ᵐ[
          normalizedCubeMeasure (originCube d 0)] FgradUnit.toField := by
    have hw' : w.toH1Function.toFun =ᵐ[
        volume.restrict (openCubeSet (originCube d m))] uv.toFun := by
      simpa only [volumeMeasureOn, uv, H1Function.sub_toFun] using hw
    have hgradVol : w.toH1Function.grad =ᵐ[
        volume.restrict (openCubeSet (originCube d m))] uv.grad :=
      H1Function.grad_ae_eq_of_toFun_ae_eq
        (isOpen_openCubeSet (originCube d m)) hw'
    have hgradNorm : w.toH1Function.grad =ᵐ[
        normalizedCubeMeasure (originCube d m)] fun x => u.grad x - v.grad x := by
      have hsmul := Measure.ae_smul_measure hgradVol
        (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹))
      simpa only [normalizedCubeMeasure, cubeMeasure,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
        uv, H1Function.sub_grad] using hsmul
    have hgradPull :=
      (centeredCubeDilationMeasurePreserving (d := d) m).quasiMeasurePreserving.ae_eq
        (by simpa only [centeredCubeDomain,
          cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
          using hgradNorm)
    have hgradPull' :
        w.toH1Function.grad ∘ centeredCubeDilation m =ᵐ[
          normalizedCubeMeasure (originCube d 0)]
            (fun x => u.grad x - v.grad x) ∘ centeredCubeDilation m := by
      simpa only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using hgradPull
    filter_upwards [hgradPull'] with x hx
    rw [Section6Dirichlet.unitH10GradientEuclideanL2Field_toField,
      scaledCenteredCubePullbackEuclideanL2Field_toField]
    change (R • (centeredCubeNormalizedPullback w).toH1Function).grad x =
      R • Fgrad.toField (centeredCubeScale m • x)
    rw [H1Function.smul_grad]
    change R • (centeredCubeNormalizedPullback w).toH1Function.grad x =
      R • Fgrad.toField (centeredCubeScale m • x)
    rw [centeredCubeNormalizedPullback_grad]
    change R • w.toH1Function.grad (centeredCubeScale m • x) =
      R • (u.grad (centeredCubeScale m • x) - v.grad (centeredCubeScale m • x))
    exact congrArg (fun z : Vec d => R • z)
      (by simpa only [Function.comp_apply] using hx)
  have hdualEq :
      paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (Section6Dirichlet.unitH10GradientEuclideanL2Field wUnit) =
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          FgradUnit :=
    paperNegativeFractionalDual_congr_ae s FiniteLpExponent.two _ _ hwgrad
  have hspectral := l2Size_le_paperNegativeFractionalDual_gradient_uniform s hs wUnit
  rw [hdualEq] at hspectral
  have hunit : l2Size (originCube d 0) wUnit.toH1Function.toFun ≤
      flatComparatorSharpSpectralConstant d *
        ENNReal.ofReal (R * alpha⁻¹ * B) :=
    hspectral.trans (mul_le_mul_right hdualGrad _)
  have hwNorm : w.toH1Function.toFun =ᵐ[
      normalizedCubeMeasure (originCube d m)] fun x => u.toFun x - v.toFun x := by
    have hsmul := Measure.ae_smul_measure hw
      (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹))
    simpa only [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
      volumeMeasureOn] using hsmul
  have hwPull :=
    (centeredCubeDilationMeasurePreserving (d := d) m).quasiMeasurePreserving.ae_eq
      (by simpa only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using hwNorm)
  have hwUnitVal : wUnit.toH1Function.toFun =ᵐ[
      normalizedCubeMeasure (originCube d 0)]
        (fun x => u.toFun x - v.toFun x) ∘ centeredCubeDilation m := by
    have hwPull' :
        w.toH1Function.toFun ∘ centeredCubeDilation m =ᵐ[
          normalizedCubeMeasure (originCube d 0)]
            (fun x => u.toFun x - v.toFun x) ∘ centeredCubeDilation m := by
      simpa only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
        using hwPull
    filter_upwards [hwPull'] with x hx
    change (R • (centeredCubeNormalizedPullback w).toH1Function).toFun x = _
    rw [H1Function.smul_toFun]
    change R * (centeredCubeNormalizedPullback w).toH1Function.toFun x = _
    rw [centeredCubeNormalizedPullback_apply]
    rw [show R = centeredCubeScale m by rfl, ← mul_assoc,
      mul_inv_cancel₀ (centeredCubeScale_ne_zero m), one_mul]
    simpa only [Function.comp_apply, centeredCubeDilation] using hx
  have huvMem : MemLp (fun x => u.toFun x - v.toFun x) 2
      (normalizedCubeMeasure (originCube d m)) :=
    u.memL2_normalizedCubeMeasure.sub v.memL2_normalizedCubeMeasure
  have huvMem' : MemLp (fun x => u.toFun x - v.toFun x) 2
      (centeredCubeDomain d m).normalizedVolume := by
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      using huvMem
  have hcomp := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
    huvMem'.aestronglyMeasurable
    (centeredCubeDilationMeasurePreserving (d := d) m)
  have hnorm :
      l2Size (originCube d 0) wUnit.toH1Function.toFun =
        eLpNorm (fun x => u.toFun x - v.toFun x) 2
          (normalizedCubeMeasure (originCube d m)) := by
    unfold l2Size
    have hmeasure : normalizedCubeMeasure (originCube d 0) =
        volume.restrict (openCubeSet (originCube d 0)) := by
      simpa only [volumeMeasureOn] using
        normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet d
    rw [← hmeasure]
    calc
      eLpNorm wUnit.toH1Function.toFun 2
          (normalizedCubeMeasure (originCube d 0)) =
        eLpNorm ((fun x => u.toFun x - v.toFun x) ∘ centeredCubeDilation m) 2
          (normalizedCubeMeasure (originCube d 0)) := eLpNorm_congr_ae hwUnitVal
      _ = eLpNorm (fun x => u.toFun x - v.toFun x) 2
          (normalizedCubeMeasure (originCube d m)) := by
        simpa only [centeredCubeDomain,
          cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
          using hcomp
  unfold cubeLpNorm
  rw [← hnorm]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (flatComparatorSharpSpectralConstant_lt_top d).ne
      ENNReal.ofReal_ne_top) hunit

private theorem ofReal_centeredCubeScale_rpow_neg_sharp
    (m : ℤ) (s : ℝ) :
    (ENNReal.ofReal (centeredCubeScale m)) ^ (-s) =
      ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) := by
  rw [ENNReal.ofReal_rpow_of_pos (centeredCubeScale_pos m)]
  congr 1
  simp only [centeredCubeScale]
  rw [← Real.rpow_intCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- The finite-`p` endpoint followed by the sharp additive-dual readout. -/
theorem exists_cubeLpNorm_sub_le_of_localCoarseGrainingLpRHS_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m n : ℤ) (hnm : n < m)
        (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
        s.1 ≤ 1 / 4 →
      ∀ (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
        (sigma : ℝ) (hsigma : 0 < sigma)
        (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma v g →
        HasH10Difference (originCube d m) u v →
      ∀ B : ℝ, 0 ≤ B →
        (ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) *
            localCoarseGrainingLpRHS C (originCube d m) n
              (by simpa [originCube] using hnm.le) a sigma hsigma g u
                s1 s s2 FiniteLpExponent.two ≤ ENNReal.ofReal B →
        cubeLpNorm (originCube d m) 2 (fun x => u.toFun x - v.toFun x) ≤
          (flatComparatorSharpSpectralConstant d *
            ENNReal.ofReal (centeredCubeScale m * sigma⁻¹ * B)).toReal := by
  obtain ⟨C, hCtop, hcg⟩ :=
    SubdiffusiveProcess.Providers.Section2.exists_generalCoarseGraining_paperDual_libraryRHS
      d hd FiniteLpExponent.two (by norm_num)
  refine ⟨C, hCtop, ?_⟩
  intro m n hnm s1 s s2 hs1s hss2 hs a sigma hsigma g hg
    u v hu hv huv B hB hRHS
  have hraw := hcg m n hnm s1 s s2 hs1s hss2 a sigma hsigma g hg
    u v hu hv huv
  have hphysical :
      ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) * ENNReal.ofReal sigma *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two (centeredCubeGradientDifferenceL2Field m u v) +
          ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeFluxDifferenceL2Field m a sigma u v) ≤
        ENNReal.ofReal B := by
    have htail := hraw.trans (by
      norm_num
      exact hRHS)
    simpa only [mul_add, mul_assoc] using htail
  have hphysical' :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) * ENNReal.ofReal sigma *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two (centeredCubeGradientDifferenceL2Field m u v) +
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeFluxDifferenceL2Field m a sigma u v) ≤
        ENNReal.ofReal B := by
    rw [ofReal_centeredCubeScale_rpow_neg_sharp]
    exact hphysical
  exact cubeLpNorm_sub_le_sharpSpectral_of_physicalCoarseGraining
    m hsigma s hs u v huv (centeredCubeFluxDifferenceL2Field m a sigma u v)
      hphysical'

/-- Complete local error loop with the sharp spectral constant. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorLocalCoarseBound_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
        s.1 ≤ 1 / 4 →
      ∀ (A : Ch02.TriadicCoeffFamily d) (sigma : ℝ) (_hsigma : 0 < sigma)
        (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) (A.coeffOn (originCube d m)) u g →
        IsScalarForcedEquation (originCube d m) sigma v g →
        HasH10Difference (originCube d m) u v →
      ∀ E1 E2 S D : ℝ,
        Ch02.HomogenizationErrorOnCube (originCube d m) s1.1 .infinity (.finite 1) A
          (scalarMatrix (d := d) sigma) ≤ E1 →
        Ch02.HomogenizationErrorOnCube (originCube d m) (s1.1 / 2)
          .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E2 →
        weightedLocalSymmetricEnergyLp (originCube d m) (m - 1) (by simp [originCube])
          (A.coeffOn (originCube d m)) u s1 s FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        cubeLpNorm (originCube d m) 2 (fun x => u.toFun x - v.toFun x) ≤
          (flatComparatorSharpSpectralConstant d *
            ENNReal.ofReal (centeredCubeScale m * sigma⁻¹ *
              (flatComparatorLocalCoarseBound C sigma s s1 s2 E1 E2 S D
                (m - 1)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_of_localCoarseGrainingLpRHS_sharp d hd
  refine ⟨C, hCtop, ?_⟩
  intro m s1 s s2 hs1s hss2 hs A sigma hsigma g hg u v hu hv huv
    E1 E2 S D hE1 hE2 hS hD
  let B := flatComparatorLocalCoarseBound C sigma s s1 s2 E1 E2 S D (m - 1)
  have hBtop : B < ∞ :=
    flatComparatorLocalCoarseBound_lt_top hCtop _ _ _ _ hss2 _ _ _ _ _
  have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  apply hmain m (m - 1) (by omega) s1 s s2 hs1s hss2 hs
    (A.coeffOn (originCube d m)) sigma hsigma g hg u v hu hv huv B.toReal hB0
  rw [ENNReal.ofReal_toReal hBtop.ne]
  exact localCoarseGrainingLpRHS_le_flatComparatorLocalCoarseBound
    (originCube d m) A C sigma hsigma g u s1 s s2 E1 E2 S D hE1 hE2
      (by simpa [originCube] using hS) hD

/-- Manuscript specialization at `(t/3,t/2,t)` with the sharp additive-dual
readout. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorManuscriptBound_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (htQuarter : t ≤ 1 / 4)
        (A : Ch02.TriadicCoeffFamily d) (sigma : ℝ) (_hsigma : 0 < sigma)
        (g : Vec d → Vec d),
      let s1 : FractionalOrder := ⟨t / 3, by positivity, by linarith⟩
      let smid : FractionalOrder := ⟨t / 2, by positivity, by linarith⟩
      let s2 : FractionalOrder := ⟨t, ht, ht1⟩
      MemCubeEuclideanFullWsp (originCube d m) s2 FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) (A.coeffOn (originCube d m)) u g →
        IsScalarForcedEquation (originCube d m) sigma v g →
        HasH10Difference (originCube d m) u v →
      ∀ E S D : ℝ,
        Ch02.HomogenizationErrorOnCube (originCube d m) (t / 6)
          .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E →
        weightedLocalSymmetricEnergyLp (originCube d m) (m - 1) (by simp [originCube])
          (A.coeffOn (originCube d m)) u s1 smid FiniteLpExponent.two ≤
            ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        cubeLpNorm (originCube d m) 2 (fun x => u.toFun x - v.toFun x) ≤
          (flatComparatorSharpSpectralConstant d *
            ENNReal.ofReal (centeredCubeScale m * sigma⁻¹ *
              (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
                (m - 1)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorLocalCoarseBound_sharp d hd
  refine ⟨C, hCtop, ?_⟩
  intro m t ht ht1 htQuarter A sigma hsigma g
  dsimp only
  intro hg u v hu hv huv E S D hE hS hD
  let s1 : FractionalOrder := ⟨t / 3, by positivity, by linarith⟩
  let smid : FractionalOrder := ⟨t / 2, by positivity, by linarith⟩
  let s2 : FractionalOrder := ⟨t, ht, ht1⟩
  have hE1 : Ch02.HomogenizationErrorOnCube (originCube d m) s1.1 .infinity
      (.finite 1) A (scalarMatrix (d := d) sigma) ≤ E := by
    have hcomp := homogenizationError_infinity_one_le_two_half
      (originCube d m) A (scalarMatrix (d := d) sigma)
      (u := s1.1) (by dsimp [s1]; positivity)
    have hsix : s1.1 / 2 = t / 6 := by dsimp [s1]; ring
    rw [hsix] at hcomp
    exact hcomp.trans hE
  apply hmain m s1 smid s2
    (by dsimp [s1, smid]; linarith) (by dsimp [smid, s2]; linarith)
    (by dsimp [smid]; linarith) A sigma hsigma g hg u v hu hv huv
      E E S D hE1
  · have heq : t / 3 / 2 = t / 6 := by ring
    simpa only [s1, heq] using hE
  · exact hS
  · exact hD

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
