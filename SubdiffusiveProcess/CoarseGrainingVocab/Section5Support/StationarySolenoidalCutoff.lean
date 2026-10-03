module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationarySolenoidalStream

@[expose] public section

/-!
# Cutting off a stationary antisymmetric stream

This module is the zero-normal counterpart of
`StationaryPotentialCutoff.lean`.  Given a smooth antisymmetric stationary
stream whose row divergence realizes a vector field, it constructs the
literal finite-cube competitor and proves both admissibility and the
pointwise localization error.

The decomposition mirrors
`Algsuperdiff/Section3/Provider/Corrector/SolenoidalApproximation.lean`.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


variable {d : ℕ}

/-- Spatial realization of a stationary stream tensor.  The value `S omega m`
is the `m`th column. -/
def stationaryStreamRealization
    (S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Fin d → Fin d → (Vec d → ℝ) :=
  fun i m x => (realize S omega x m).toVec i

@[simp] theorem stationaryStreamRealization_apply
    (S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (i m : Fin d) (x : Vec d) :
    stationaryStreamRealization S omega i m x =
      (realize S omega x m).toVec i := rfl

/-- Boundary remainder produced by differentiating the cutoff. -/
def stationaryStreamRemainder (Q : TriadicCube d) (L : ℕ)
    (S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : Vec d) : HilbertVec d :=
  ∑ m : Fin d,
    fderiv ℝ (stationaryPotentialCutoff Q L).toFun x (basisVec m) •
      realize S omega x m

/-- The cutoff stream competitor, written after the product-rule expansion. -/
def stationaryLocalStreamApprox (Q : TriadicCube d) (L : ℕ)
    (S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d)
    (D : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : Vec d) : Vec d :=
  fun i =>
    (stationaryPotentialCutoff Q L).toFun x *
        (realize D omega x).toVec i +
      stationaryStreamRemainder Q L S omega x i

private theorem hilbertVec_sum_apply {I : Type*} (s : Finset I)
    (f : I → HilbertVec d) (i : Fin d) :
    (∑ m ∈ s, f m) i = ∑ m ∈ s, f m i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a t ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

theorem stationaryStreamRemainder_apply
    (Q : TriadicCube d) (L : ℕ)
    (S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : Vec d) (i : Fin d) :
    stationaryStreamRemainder Q L S omega x i =
      ∑ m : Fin d,
        fderiv ℝ (stationaryPotentialCutoff Q L).toFun x (basisVec m) *
          stationaryStreamRealization S omega i m x := by
  rw [stationaryStreamRemainder, hilbertVec_sum_apply]
  apply Finset.sum_congr rfl
  intro m _
  rw [PiLp.smul_apply, smul_eq_mul]
  rfl

theorem ofVec_stationaryLocalStreamApprox_sub_realize
    (Q : TriadicCube d) (L : ℕ)
    (S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d)
    (D : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
        realize D omega x =
      ((stationaryPotentialCutoff Q L).toFun x - 1) •
          realize D omega x +
        stationaryStreamRemainder Q L S omega x := by
  ext i
  simp only [stationaryLocalStreamApprox, HilbertVec.ofVec, PiLp.sub_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The cutoff competitor is exactly the divergence of the cutoff
antisymmetric tensor and therefore has zero normal trace. -/
theorem isSolenoidalZeroNormalTraceOn_stationaryLocalStreamApprox
    (Q : TriadicCube d) (L : ℕ)
    {S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d}
    {D : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d} {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hstreamSmooth : ∀ i m, ContDiff ℝ (⊤ : ℕ∞)
      (stationaryStreamRealization S omega i m))
    (hstreamAnti : ∀ i m,
      stationaryStreamRealization S omega m i =
        -stationaryStreamRealization S omega i m)
    (hstreamDiv : ∀ x : Vec d,
      streamDivergence (stationaryStreamRealization S omega) x =
        (realize D omega x).toVec) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (stationaryLocalStreamApprox Q L S D omega) := by
  have hbase : IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (streamDivergence (cutoffStream
        (stationaryPotentialCutoff Q L).toFun
        (stationaryStreamRealization S omega) 0)) :=
    isSolenoidalZeroNormalTraceOn_cutoffStream
      (stationaryPotentialCutoff Q L).smooth
      (stationaryPotentialCutoff Q L).hasCompactSupport
      (stationaryPotentialCutoff_tsupport_subset Q L)
      hstreamSmooth hstreamAnti (by simp)
  refine (show streamDivergence (cutoffStream
      (stationaryPotentialCutoff Q L).toFun
      (stationaryStreamRealization S omega) 0) =
        stationaryLocalStreamApprox Q L S D omega from ?_) ▸ hbase
  funext x i
  rw [streamDivergence_cutoffStream_apply
    (((stationaryPotentialCutoff Q L).smooth.differentiable
      (by simp)).differentiableAt)
    (fun a b => (((hstreamSmooth a b).differentiable
      (by simp)).differentiableAt)) i,
    hstreamDiv x]
  simp only [stationaryLocalStreamApprox, stationaryStreamRemainder_apply,
    Pi.zero_apply, sub_zero, streamCoordDeriv]

/-- Pointwise control of the cutoff-stream remainder. -/
theorem norm_stationaryStreamRemainder_le
    (Q : TriadicCube d) (L : ℕ)
    (S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : Vec d) :
    ‖stationaryStreamRemainder Q L S omega x‖ ≤
      stationaryPotentialCutoffGradBound Q L * ‖realize S omega x‖ := by
  have hsum := norm_sum_le Finset.univ (fun m : Fin d =>
    fderiv ℝ (stationaryPotentialCutoff Q L).toFun x (basisVec m) •
      realize S omega x m)
  calc
    ‖stationaryStreamRemainder Q L S omega x‖ ≤
        ∑ m : Fin d,
          ‖fderiv ℝ (stationaryPotentialCutoff Q L).toFun x (basisVec m) •
            realize S omega x m‖ := by
      simpa only [stationaryStreamRemainder] using hsum
    _ ≤ ∑ _m : Fin d,
        (quantitativeCubeCutoffGradientConst d /
          ((stationaryCutoffOuterRatio L - stationaryCutoffInnerRatio L) *
            cubeRadius Q)) * ‖realize S omega x‖ := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_smul, Real.norm_eq_abs]
      have hderiv := (stationaryPotentialCutoff Q L).gradient_bound x
      have hbasis : ‖(basisVec m : Vec d)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
        by_cases hj : j = m
        · subst hj
          simp [basisVec]
        · simp [basisVec, hj]
      have happly := (fderiv ℝ
        (stationaryPotentialCutoff Q L).toFun x).le_opNorm (basisVec m)
      have hcoord :
          |fderiv ℝ (stationaryPotentialCutoff Q L).toFun x
              (basisVec m)| ≤
            quantitativeCubeCutoffGradientConst d /
              ((stationaryCutoffOuterRatio L - stationaryCutoffInnerRatio L) *
                cubeRadius Q) := by
        rw [← Real.norm_eq_abs]
        calc
          ‖fderiv ℝ (stationaryPotentialCutoff Q L).toFun x
              (basisVec m)‖ ≤
              ‖fderiv ℝ (stationaryPotentialCutoff Q L).toFun x‖ *
                ‖(basisVec m : Vec d)‖ := happly
          _ ≤ ‖fderiv ℝ (stationaryPotentialCutoff Q L).toFun x‖ := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left
              hbasis (norm_nonneg _)
          _ ≤ _ := hderiv
      have hentry : ‖realize S omega x m‖ ≤ ‖realize S omega x‖ :=
        norm_le_pi_norm (realize S omega x) m
      exact mul_le_mul hcoord hentry (norm_nonneg _)
        ((abs_nonneg _).trans hcoord)
    _ = stationaryPotentialCutoffGradBound Q L *
        ‖realize S omega x‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, stationaryPotentialCutoffGradBound]
      ring

/-- Pointwise squared error of the zero-normal stream cutoff. -/
theorem norm_sq_stationaryLocalStreamApprox_sub_le
    (Q : TriadicCube d) (L : ℕ)
    (S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d)
    (D : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {x : Vec d} (hx : x ∈ cubeSet Q) :
    ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
        realize D omega x‖ ^ 2 ≤
      2 * (stationaryPotentialBoundaryStrip Q L).indicator
          (fun y => ‖realize D omega y‖ ^ 2) x +
        2 * stationaryPotentialCutoffGradBound Q L ^ 2 *
          ‖realize S omega x‖ ^ 2 := by
  have hdec := ofVec_stationaryLocalStreamApprox_sub_realize
    Q L S D omega x
  have hsecond := norm_stationaryStreamRemainder_le Q L S omega x
  have hgb0 := stationaryPotentialCutoffGradBound_nonneg Q L
  by_cases hmem : x ∈
      scaledClosedCubeSet Q (stationaryCutoffInnerRatio L)
  · have hone : (stationaryPotentialCutoff Q L).toFun x = 1 :=
      (stationaryPotentialCutoff Q L).eq_one_on_inner x hmem
    have hind : (stationaryPotentialBoundaryStrip Q L).indicator
        (fun y => ‖realize D omega y‖ ^ 2) x = 0 :=
      Set.indicator_of_notMem (fun h => h.2 hmem) _
    have hle :
        ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
          realize D omega x‖ ≤
        stationaryPotentialCutoffGradBound Q L * ‖realize S omega x‖ := by
      rw [hdec, hone]
      simpa using hsecond
    rw [hind]
    nlinarith [norm_nonneg
      (HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
        realize D omega x),
      mul_nonneg hgb0 (norm_nonneg (realize S omega x))]
  · have hxmem : x ∈ stationaryPotentialBoundaryStrip Q L :=
      Set.mem_diff_of_mem hx hmem
    have hind : (stationaryPotentialBoundaryStrip Q L).indicator
        (fun y => ‖realize D omega y‖ ^ 2) x =
          ‖realize D omega x‖ ^ 2 := Set.indicator_of_mem hxmem _
    have hcut : ‖(stationaryPotentialCutoff Q L).toFun x - 1‖ ≤ 1 := by
      have h0 := (stationaryPotentialCutoff Q L).nonneg x
      have h1 := (stationaryPotentialCutoff Q L).le_one x
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hfirst :
        ‖((stationaryPotentialCutoff Q L).toFun x - 1) •
          realize D omega x‖ ≤ ‖realize D omega x‖ := by
      rw [norm_smul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hcut (norm_nonneg (realize D omega x))
    have hle :
        ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
          realize D omega x‖ ≤
        ‖realize D omega x‖ +
          stationaryPotentialCutoffGradBound Q L *
            ‖realize S omega x‖ := by
      rw [hdec]
      exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
    rw [hind]
    nlinarith [norm_nonneg
      (HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
        realize D omega x), norm_nonneg (realize D omega x),
      mul_nonneg hgb0 (norm_nonneg (realize S omega x)),
      sq_nonneg (‖realize D omega x‖ -
        stationaryPotentialCutoffGradBound Q L * ‖realize S omega x‖)]

/-- Expected unnormalized error of the cutoff-stream competitor.  This is the
zero-normal analogue of
`integral_setIntegral_normSq_stationaryRepresentativeLocalGrad_sub_le`.
The first term is confined to the boundary strip; the second is the price of
differentiating the cutoff tensor. -/
theorem integral_setIntegral_normSq_stationaryLocalStreamApprox_sub_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Q : TriadicCube d) (L : ℕ)
    {S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d}
    {D : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 M.P.toMeasure)
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 M.P.toMeasure) :
    ∫ omega, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
          realize D omega x‖ ^ 2) ∂M.P.toMeasure ≤
      2 * ((volume (stationaryPotentialBoundaryStrip Q L)).toReal *
          ∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure) +
        2 * stationaryPotentialCutoffGradBound Q L ^ 2 *
          (cubeVolume Q * ∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure) := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hBfin := volume_stationaryPotentialBoundaryStrip_ne_top Q L
  have hBmeas := measurableSet_stationaryPotentialBoundaryStrip Q L
  let G := stationaryPotentialCutoffGradBound Q L
  have hdomint : Integrable (fun omega =>
      2 * (∫ x in stationaryPotentialBoundaryStrip Q L,
        ‖realize D omega x‖ ^ 2) +
      2 * G ^ 2 * ∫ x in cubeSet Q, ‖realize S omega x‖ ^ 2)
      M.P.toMeasure :=
    ((integrable_setIntegral_normSq_realize M hBfin hDm hD).const_mul 2).add
      ((integrable_setIntegral_normSq_realize M hQfin hSm hS).const_mul
        (2 * G ^ 2))
  have hmono :
      ∫ omega, (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryLocalStreamApprox Q L S D omega x) -
            realize D omega x‖ ^ 2) ∂M.P.toMeasure ≤
        ∫ omega, (2 *
            (∫ x in stationaryPotentialBoundaryStrip Q L,
              ‖realize D omega x‖ ^ 2) +
          2 * G ^ 2 * ∫ x in cubeSet Q,
            ‖realize S omega x‖ ^ 2) ∂M.P.toMeasure := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => by positivity)
      hdomint ?_
    filter_upwards [ae_memLp_two_realize M hBfin hDm hD,
      ae_memLp_two_realize M hQfin hSm hS,
      ae_memLp_two_realize M hQfin hDm hD] with omega hDB hSQ hDQ
    have hDBint : Integrable (fun x => ‖realize D omega x‖ ^ 2)
        (volume.restrict (stationaryPotentialBoundaryStrip Q L)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hDm omega).aestronglyMeasurable).1 hDB
    have hSQint : Integrable (fun x => ‖realize S omega x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hSm omega).aestronglyMeasurable).1 hSQ
    have hindvol : Integrable
        ((stationaryPotentialBoundaryStrip Q L).indicator
          fun y => ‖realize D omega y‖ ^ 2) volume :=
      MeasureTheory.IntegrableOn.integrable_indicator hDBint hBmeas
    have hindint : Integrable
        ((stationaryPotentialBoundaryStrip Q L).indicator
          fun y => ‖realize D omega y‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      hindvol.mono_measure Measure.restrict_le_self
    have hbound : Integrable (fun x =>
        2 * (stationaryPotentialBoundaryStrip Q L).indicator
              (fun y => ‖realize D omega y‖ ^ 2) x +
          2 * G ^ 2 * ‖realize S omega x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (hindint.const_mul 2).add (hSQint.const_mul (2 * G ^ 2))
    have hinner :
        (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryLocalStreamApprox Q L S D omega x) -
            realize D omega x‖ ^ 2) ≤
        ∫ x in cubeSet Q,
          (2 * (stationaryPotentialBoundaryStrip Q L).indicator
                (fun y => ‖realize D omega y‖ ^ 2) x +
            2 * G ^ 2 * ‖realize S omega x‖ ^ 2) := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => by positivity) hbound ?_
      refine (ae_restrict_iff' (measurableSet_cubeSet Q)).2 ?_
      filter_upwards with x hx
      simpa only [G] using
        norm_sq_stationaryLocalStreamApprox_sub_le Q L S D omega hx
    refine hinner.trans (le_of_eq ?_)
    rw [integral_add (hindint.const_mul 2)
        (hSQint.const_mul (2 * G ^ 2)),
      integral_const_mul, integral_const_mul,
      setIntegral_indicator hBmeas,
      Set.inter_eq_self_of_subset_right
        (stationaryPotentialBoundaryStrip_subset_cubeSet Q L)]
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add
      ((integrable_setIntegral_normSq_realize M hBfin hDm hD).const_mul 2)
      ((integrable_setIntegral_normSq_realize M hQfin hSm hS).const_mul
        (2 * G ^ 2)),
    integral_const_mul, integral_const_mul,
    integral_setIntegral_normSq_realize M hBfin hDm hD,
    integral_setIntegral_normSq_realize M hQfin hSm hS,
    volume_cubeSet_toReal]

/-- Normalized expected cutoff-stream error. -/
theorem normalized_integral_setIntegral_normSq_stationaryLocalStreamApprox_sub_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Q : TriadicCube d) (L : ℕ)
    {S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Fin d → HilbertVec d}
    {D : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 M.P.toMeasure)
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 M.P.toMeasure) :
    (cubeVolume Q)⁻¹ *
        (∫ omega, (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryLocalStreamApprox Q L S D omega x) -
            realize D omega x‖ ^ 2) ∂M.P.toMeasure) ≤
      (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
          (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure) +
        2 * stationaryPotentialCutoffGradBound Q L ^ 2 *
          (∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure) := by
  let V := cubeVolume Q
  let B := (volume (stationaryPotentialBoundaryStrip Q L)).toReal
  let R := (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ))
  let ID := ∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure
  let IS := ∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure
  let G := stationaryPotentialCutoffGradBound Q L
  let A := ∫ omega, (∫ x in cubeSet Q,
    ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
      realize D omega x‖ ^ 2) ∂M.P.toMeasure
  have hV : 0 < V := cubeVolume_pos Q
  have hID : 0 ≤ ID := integral_nonneg fun _ => by positivity
  have hraw : A ≤ 2 * (B * ID) + 2 * G ^ 2 * (V * IS) := by
    exact integral_setIntegral_normSq_stationaryLocalStreamApprox_sub_le
      M Q L hSm hS hDm hD
  have hscaled := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hV.le)
  have hstrip : B ≤ R / 2 * V := by
    simpa only [B, R, div_mul_eq_mul_div, mul_assoc] using
      volume_stationaryPotentialBoundaryStrip_toReal_le Q L
  have hstripScaled : 2 * V⁻¹ * B ≤ R := by
    calc
      2 * V⁻¹ * B ≤ 2 * V⁻¹ * (R / 2 * V) :=
        mul_le_mul_of_nonneg_left hstrip
          (mul_nonneg (by norm_num) (inv_nonneg.mpr hV.le))
      _ = R := by field_simp
  have hstripMoment : (2 * V⁻¹ * B) * ID ≤ R * ID :=
    mul_le_mul_of_nonneg_right hstripScaled hID
  change V⁻¹ * A ≤ R * ID + 2 * G ^ 2 * IS
  calc
    V⁻¹ * A ≤ V⁻¹ *
        (2 * (B * ID) + 2 * G ^ 2 * (V * IS)) := hscaled
    _ = (2 * V⁻¹ * B) * ID + 2 * G ^ 2 * IS := by field_simp
    _ ≤ R * ID + 2 * G ^ 2 * IS := add_le_add hstripMoment le_rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
