module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryMollifiedDecorrelation

@[expose] public section

/-!
# Approximate antisymmetric streams for the one-step solenoidal remainder

This module completes the topology-free stream construction. A small product mollifier approximates the solenoidal remainder, a large product
mollifier is killed by finite-range decorrelation, and the explicit
two-scale divergence kernel realizes their difference as the divergence of
an antisymmetric stationary stream.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Integrability of the literal cutoff-stream error against an arbitrary stationary
`L²` target. -/
theorem integrable_setIntegral_normSq_stationaryLocalStreamApprox_target {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (L : ℕ)
    {S : _root_.SubdiffusiveProcess.Model.PotentialSample d → Fin d → HilbertVec d}
    {D J : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 M.P.toMeasure)
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 M.P.toMeasure)
    (hJm : StronglyMeasurable J) (hJ : MemLp J 2 M.P.toMeasure) :
    Integrable (fun omega => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
        realize J omega x‖ ^ 2) M.P.toMeasure := by
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d := fun omega => D omega - J omega
  let G : ℝ := stationaryPotentialCutoffGradBound Q L
  have hZm : StronglyMeasurable Z := hDm.sub hJm
  have hZ : MemLp Z 2 M.P.toMeasure := hD.sub hJ
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hmajor : Integrable (fun omega =>
      3 * (∫ x in cubeSet Q, ‖realize D omega x‖ ^ 2) +
      3 * G ^ 2 * (∫ x in cubeSet Q, ‖realize S omega x‖ ^ 2) +
      3 * (∫ x in cubeSet Q, ‖realize Z omega x‖ ^ 2)) M.P.toMeasure :=
    (((integrable_setIntegral_normSq_realize M hQfin hDm hD).const_mul 3).add
      ((integrable_setIntegral_normSq_realize M hQfin hSm hS).const_mul
        (3 * G ^ 2))).add
      ((integrable_setIntegral_normSq_realize M hQfin hZm hZ).const_mul 3)
  have hcut : Continuous (stationaryPotentialCutoff Q L).toFun :=
    (stationaryPotentialCutoff Q L).smooth.continuous
  have hcoef : StronglyMeasurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      (stationaryPotentialCutoff Q L).toFun z.2 - 1) :=
    ((hcut.comp continuous_snd).stronglyMeasurable).sub stronglyMeasurable_const
  have hSreal := stronglyMeasurable_uncurry_realize hSm
  have hrem : StronglyMeasurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      stationaryStreamRemainder Q L S z.1 z.2) := by
    change StronglyMeasurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      ∑ m : Fin d,
        fderiv ℝ (stationaryPotentialCutoff Q L).toFun z.2 (basisVec m) •
          realize S z.1 z.2 m)
    have hterm : ∀ m : Fin d, StronglyMeasurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
        fderiv ℝ (stationaryPotentialCutoff Q L).toFun z.2 (basisVec m) •
          realize S z.1 z.2 m) := by
      intro m
      have hderiv : StronglyMeasurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
          fderiv ℝ (stationaryPotentialCutoff Q L).toFun z.2 (basisVec m)) :=
        ((((stationaryPotentialCutoff Q L).smooth.continuous_fderiv (by simp)).clm_apply
          continuous_const).comp continuous_snd).stronglyMeasurable
      exact hderiv.smul ((continuous_apply m).comp_stronglyMeasurable hSreal)
    have hsum := Finset.stronglyMeasurable_sum Finset.univ (fun m _hm => hterm m)
    convert hsum using 1
    funext z
    simp only [Finset.sum_apply]
  have hjoint : StronglyMeasurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D z.1 z.2) -
        realize J z.1 z.2) := by
    have hright : StronglyMeasurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
        ((stationaryPotentialCutoff Q L).toFun z.2 - 1) • realize D z.1 z.2 +
          stationaryStreamRemainder Q L S z.1 z.2 + realize Z z.1 z.2) :=
      ((hcoef.smul (stronglyMeasurable_uncurry_realize hDm)).add hrem).add
        (stronglyMeasurable_uncurry_realize hZm)
    convert hright using 1
    funext z
    rw [show realize Z z.1 z.2 = realize D z.1 z.2 - realize J z.1 z.2 by rfl]
    rw [← ofVec_stationaryLocalStreamApprox_sub_realize Q L S D z.1 z.2]
    abel
  have htargetMeas : StronglyMeasurable (fun omega => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
        realize J omega x‖ ^ 2) := by
    simpa only [Measure.restrict_apply_univ] using!
      (hjoint.norm.pow 2).integral_prod_right'
        (ν := volume.restrict (cubeSet Q))
  apply hmajor.mono' htargetMeas.aestronglyMeasurable
  filter_upwards [ae_memLp_two_realize M hQfin hDm hD,
    ae_memLp_two_realize M hQfin hSm hS,
    ae_memLp_two_realize M hQfin hZm hZ] with omega hDomega hSomega hZomega
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => by positivity)]
  have hinner : ∀ x : Vec d,
      ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
        realize J omega x‖ ^ 2 ≤
      3 * ‖realize D omega x‖ ^ 2 +
        3 * G ^ 2 * ‖realize S omega x‖ ^ 2 +
        3 * ‖realize Z omega x‖ ^ 2 := by
    intro x
    have hcut0 := (stationaryPotentialCutoff Q L).nonneg x
    have hcut1 := (stationaryPotentialCutoff Q L).le_one x
    have hcoefLe : ‖(stationaryPotentialCutoff Q L).toFun x - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
    have hremLe := norm_stationaryStreamRemainder_le Q L S omega x
    have hG0 : 0 ≤ G := stationaryPotentialCutoffGradBound_nonneg Q L
    have hdecomp := ofVec_stationaryLocalStreamApprox_sub_realize
      Q L S D omega x
    have htri :
        ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
          realize J omega x‖ ≤
        ‖realize D omega x‖ + G * ‖realize S omega x‖ +
          ‖realize Z omega x‖ := by
      have heq : HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
          realize J omega x =
          (((stationaryPotentialCutoff Q L).toFun x - 1) • realize D omega x +
            stationaryStreamRemainder Q L S omega x) + realize Z omega x := by
        rw [show realize Z omega x = realize D omega x - realize J omega x by rfl,
          ← hdecomp]
        abel
      rw [heq]
      have hfirst :
          ‖((stationaryPotentialCutoff Q L).toFun x - 1) • realize D omega x‖ ≤
            ‖realize D omega x‖ := by
        rw [norm_smul]
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right hcoefLe (norm_nonneg _)
      calc
        _ ≤ ‖((stationaryPotentialCutoff Q L).toFun x - 1) • realize D omega x‖ +
            ‖stationaryStreamRemainder Q L S omega x‖ +
            ‖realize Z omega x‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ _ := add_le_add (add_le_add hfirst hremLe) le_rfl
    let a : ℝ := ‖realize D omega x‖
    let b : ℝ := G * ‖realize S omega x‖
    let c : ℝ := ‖realize Z omega x‖
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hthree : (a + b + c) ^ 2 ≤
        3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    calc
      _ ≤ (‖realize D omega x‖ + G * ‖realize S omega x‖ +
          ‖realize Z omega x‖) ^ 2 := hsquare
      _ ≤ _ := by
        dsimp only [a, b, c] at hthree
        ring_nf at hthree ⊢
        exact hthree
  have hDint : Integrable (fun x => ‖realize D omega x‖ ^ 2)
      (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm
      (stronglyMeasurable_realize hDm omega).aestronglyMeasurable).1 hDomega
  have hSint : Integrable (fun x => ‖realize S omega x‖ ^ 2)
      (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm
      (stronglyMeasurable_realize hSm omega).aestronglyMeasurable).1 hSomega
  have hZint : Integrable (fun x => ‖realize Z omega x‖ ^ 2)
      (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm
      (stronglyMeasurable_realize hZm omega).aestronglyMeasurable).1 hZomega
  have hD3 := hDint.const_mul 3
  have hS3 := hSint.const_mul (3 * G ^ 2)
  have hZ3 := hZint.const_mul 3
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => by positivity)
    ((hD3.add hS3).add hZ3) (Filter.Eventually.of_forall hinner)
  calc
    _ ≤ ∫ x in cubeSet Q,
        (3 * ‖realize D omega x‖ ^ 2 +
          3 * G ^ 2 * ‖realize S omega x‖ ^ 2 +
          3 * ‖realize Z omega x‖ ^ 2) := hmono
    _ = _ := by
      let fD : Vec d → ℝ := fun x => 3 * ‖realize D omega x‖ ^ 2
      let fS : Vec d → ℝ := fun x => 3 * G ^ 2 * ‖realize S omega x‖ ^ 2
      let fZ : Vec d → ℝ := fun x => 3 * ‖realize Z omega x‖ ^ 2
      have hout := integral_add ((show Integrable fD _ from hD3).add
        (show Integrable fS _ from hS3)) (show Integrable fZ _ from hZ3)
      have hin := integral_add (show Integrable fD _ from hD3)
        (show Integrable fS _ from hS3)
      calc
        _ = (∫ x in cubeSet Q, fD x + fS x) +
            ∫ x in cubeSet Q, fZ x := by
          simpa only [fD, fS, fZ, Pi.add_apply] using! hout
        _ = ((∫ x in cubeSet Q, fD x) + ∫ x in cubeSet Q, fS x) +
            ∫ x in cubeSet Q, fZ x := by rw [hin]
        _ = _ := by
          dsimp only [fD, fS, fZ]
          rw [integral_const_mul, integral_const_mul, integral_const_mul]

/-- For almost every sample, the literal cutoff-stream error is an honest
spatial `L²` field.  This rules out the Bochner junk branch before the
Neumann Young comparison is applied. -/
theorem ae_memLp_two_stationaryLocalStreamApprox_sub_target
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (L : ℕ)
    {S : _root_.SubdiffusiveProcess.Model.PotentialSample d → Fin d → HilbertVec d}
    {D J : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 M.P.toMeasure)
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 M.P.toMeasure)
    (hJm : StronglyMeasurable J) (hJ : MemLp J 2 M.P.toMeasure) :
    ∀ᵐ omega ∂M.P.toMeasure,
      MemLp (fun x =>
        HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
          realize J omega x) 2 (volume.restrict (cubeSet Q)) := by
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d := fun omega => D omega - J omega
  let G : ℝ := stationaryPotentialCutoffGradBound Q L
  have hZm : StronglyMeasurable Z := hDm.sub hJm
  have hZ : MemLp Z 2 M.P.toMeasure := hD.sub hJ
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  filter_upwards [ae_memLp_two_realize M hQfin hDm hD,
    ae_memLp_two_realize M hQfin hSm hS,
    ae_memLp_two_realize M hQfin hZm hZ]
    with omega hDomega hSomega hZomega
  have hDreal := stronglyMeasurable_realize hDm omega
  have hSreal := stronglyMeasurable_realize hSm omega
  have hZreal := stronglyMeasurable_realize hZm omega
  have hcut : Continuous (stationaryPotentialCutoff Q L).toFun :=
    (stationaryPotentialCutoff Q L).smooth.continuous
  have hcoef : StronglyMeasurable (fun x : Vec d =>
      (stationaryPotentialCutoff Q L).toFun x - 1) :=
    hcut.stronglyMeasurable.sub stronglyMeasurable_const
  have hrem : StronglyMeasurable (fun x : Vec d =>
      stationaryStreamRemainder Q L S omega x) := by
    change StronglyMeasurable (fun x : Vec d =>
      ∑ m : Fin d,
        fderiv ℝ (stationaryPotentialCutoff Q L).toFun x (basisVec m) •
          realize S omega x m)
    have hterm : ∀ m : Fin d, StronglyMeasurable (fun x : Vec d =>
        fderiv ℝ (stationaryPotentialCutoff Q L).toFun x (basisVec m) •
          realize S omega x m) := by
      intro m
      have hderiv : StronglyMeasurable (fun x : Vec d =>
          fderiv ℝ (stationaryPotentialCutoff Q L).toFun x (basisVec m)) :=
        (((stationaryPotentialCutoff Q L).smooth.continuous_fderiv
          (by simp)).clm_apply continuous_const).stronglyMeasurable
      exact hderiv.smul ((continuous_apply m).comp_stronglyMeasurable hSreal)
    have hsum := Finset.stronglyMeasurable_sum Finset.univ
      (fun m _hm => hterm m)
    convert hsum using 1
    funext x
    simp only [Finset.sum_apply]
  have htarget : StronglyMeasurable (fun x : Vec d =>
      HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
        realize J omega x) := by
    have hright : StronglyMeasurable (fun x : Vec d =>
        ((stationaryPotentialCutoff Q L).toFun x - 1) • realize D omega x +
          stationaryStreamRemainder Q L S omega x + realize Z omega x) :=
      ((hcoef.smul hDreal).add hrem).add hZreal
    convert hright using 1
    funext x
    rw [show realize Z omega x = realize D omega x - realize J omega x by rfl]
    rw [← ofVec_stationaryLocalStreamApprox_sub_realize Q L S D omega x]
    abel
  have hDint : Integrable (fun x => ‖realize D omega x‖ ^ 2)
      (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm hDreal.aestronglyMeasurable).1 hDomega
  have hSint : Integrable (fun x => ‖realize S omega x‖ ^ 2)
      (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm hSreal.aestronglyMeasurable).1 hSomega
  have hZint : Integrable (fun x => ‖realize Z omega x‖ ^ 2)
      (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm hZreal.aestronglyMeasurable).1 hZomega
  have hmajor : Integrable (fun x =>
      3 * ‖realize D omega x‖ ^ 2 +
        3 * G ^ 2 * ‖realize S omega x‖ ^ 2 +
        3 * ‖realize Z omega x‖ ^ 2)
      (volume.restrict (cubeSet Q)) :=
    ((hDint.const_mul 3).add (hSint.const_mul (3 * G ^ 2))).add
      (hZint.const_mul 3)
  have hinner : ∀ x : Vec d,
      ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
        realize J omega x‖ ^ 2 ≤
      3 * ‖realize D omega x‖ ^ 2 +
        3 * G ^ 2 * ‖realize S omega x‖ ^ 2 +
        3 * ‖realize Z omega x‖ ^ 2 := by
    intro x
    have hcut0 := (stationaryPotentialCutoff Q L).nonneg x
    have hcut1 := (stationaryPotentialCutoff Q L).le_one x
    have hcoefLe : ‖(stationaryPotentialCutoff Q L).toFun x - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
    have hremLe := norm_stationaryStreamRemainder_le Q L S omega x
    have hdecomp := ofVec_stationaryLocalStreamApprox_sub_realize
      Q L S D omega x
    have htri :
        ‖HilbertVec.ofVec (stationaryLocalStreamApprox Q L S D omega x) -
          realize J omega x‖ ≤
        ‖realize D omega x‖ + G * ‖realize S omega x‖ +
          ‖realize Z omega x‖ := by
      have heq : HilbertVec.ofVec
            (stationaryLocalStreamApprox Q L S D omega x) -
          realize J omega x =
          (((stationaryPotentialCutoff Q L).toFun x - 1) • realize D omega x +
            stationaryStreamRemainder Q L S omega x) + realize Z omega x := by
        rw [show realize Z omega x = realize D omega x - realize J omega x by rfl,
          ← hdecomp]
        abel
      rw [heq]
      have hfirst :
          ‖((stationaryPotentialCutoff Q L).toFun x - 1) • realize D omega x‖ ≤
            ‖realize D omega x‖ := by
        rw [norm_smul]
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right hcoefLe (norm_nonneg _)
      exact (norm_add_le _ _).trans
        ((add_le_add (norm_add_le _ _) le_rfl).trans
          (add_le_add (add_le_add hfirst hremLe) le_rfl))
    let a : ℝ := ‖realize D omega x‖
    let b : ℝ := G * ‖realize S omega x‖
    let c : ℝ := ‖realize Z omega x‖
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hthree : (a + b + c) ^ 2 ≤
        3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    calc
      _ ≤ (‖realize D omega x‖ + G * ‖realize S omega x‖ +
          ‖realize Z omega x‖) ^ 2 := hsquare
      _ ≤ _ := by
        dsimp only [a, b, c] at hthree
        ring_nf at hthree ⊢
        exact hthree
  apply (memLp_two_iff_integrable_sq_norm htarget.aestronglyMeasurable).2
  apply hmajor.mono' (htarget.norm.pow 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hinner x


/-- Expected normalized error when the cutoff stream diverges to an
auxiliary field `D` which is only `L²`-close to the target `J`. -/
theorem normalized_integral_setIntegral_normSq_stationaryLocalStreamApprox_target_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (L : ℕ)
    {S : _root_.SubdiffusiveProcess.Model.PotentialSample d → Fin d → HilbertVec d}
    {D J : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 M.P.toMeasure)
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 M.P.toMeasure)
    (hJm : StronglyMeasurable J) (hJ : MemLp J 2 M.P.toMeasure) :
    (cubeVolume Q)⁻¹ *
        (∫ omega, (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryLocalStreamApprox Q L S D omega x) -
            realize J omega x‖ ^ 2) ∂M.P.toMeasure) ≤
      2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
          (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure) +
        2 * stationaryPotentialCutoffGradBound Q L ^ 2 *
          (∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure)) +
      2 * ∫ omega, ‖D omega - J omega‖ ^ 2 ∂M.P.toMeasure := by
  let V := cubeVolume Q
  let B := stationaryPotentialBoundaryStrip Q L
  let G := stationaryPotentialCutoffGradBound Q L
  let gap : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d := fun omega => D omega - J omega
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hBfin := volume_stationaryPotentialBoundaryStrip_ne_top Q L
  have hBmeas := measurableSet_stationaryPotentialBoundaryStrip Q L
  have hgapm : StronglyMeasurable gap := hDm.sub hJm
  have hgap : MemLp gap 2 M.P.toMeasure := hD.sub hJ
  have hdomint : Integrable (fun omega =>
      4 * (∫ x in B, ‖realize D omega x‖ ^ 2) +
      4 * G ^ 2 * (∫ x in cubeSet Q, ‖realize S omega x‖ ^ 2) +
      2 * (∫ x in cubeSet Q, ‖realize gap omega x‖ ^ 2))
      M.P.toMeasure :=
    (((integrable_setIntegral_normSq_realize M hBfin hDm hD).const_mul 4).add
      ((integrable_setIntegral_normSq_realize M hQfin hSm hS).const_mul
        (4 * G ^ 2))).add
      ((integrable_setIntegral_normSq_realize M hQfin hgapm hgap).const_mul 2)
  have hmono :
      ∫ omega, (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryLocalStreamApprox Q L S D omega x) -
            realize J omega x‖ ^ 2) ∂M.P.toMeasure ≤
        ∫ omega, (4 * (∫ x in B, ‖realize D omega x‖ ^ 2) +
          4 * G ^ 2 * (∫ x in cubeSet Q, ‖realize S omega x‖ ^ 2) +
          2 * (∫ x in cubeSet Q, ‖realize gap omega x‖ ^ 2))
          ∂M.P.toMeasure := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => by positivity)
      hdomint ?_
    filter_upwards [ae_memLp_two_realize M hBfin hDm hD,
      ae_memLp_two_realize M hQfin hSm hS,
      ae_memLp_two_realize M hQfin hgapm hgap] with omega hDB hSQ hgapQ
    have hDBint : Integrable (fun x => ‖realize D omega x‖ ^ 2)
        (volume.restrict B) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hDm omega).aestronglyMeasurable).1 hDB
    have hSQint : Integrable (fun x => ‖realize S omega x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hSm omega).aestronglyMeasurable).1 hSQ
    have hgapQint : Integrable (fun x => ‖realize gap omega x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hgapm omega).aestronglyMeasurable).1 hgapQ
    have hindvol : Integrable
        (B.indicator fun y => ‖realize D omega y‖ ^ 2) volume :=
      IntegrableOn.integrable_indicator hDBint hBmeas
    have hindint : Integrable
        (B.indicator fun y => ‖realize D omega y‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      hindvol.mono_measure Measure.restrict_le_self
    have hrhsInt : Integrable (fun x =>
        4 * B.indicator (fun y => ‖realize D omega y‖ ^ 2) x +
          4 * G ^ 2 * ‖realize S omega x‖ ^ 2 +
          2 * ‖realize gap omega x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      ((hindint.const_mul 4).add (hSQint.const_mul (4 * G ^ 2))).add
        (hgapQint.const_mul 2)
    have hinner :
        (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryLocalStreamApprox Q L S D omega x) -
            realize J omega x‖ ^ 2) ≤
          ∫ x in cubeSet Q,
            (4 * B.indicator (fun y => ‖realize D omega y‖ ^ 2) x +
              4 * G ^ 2 * ‖realize S omega x‖ ^ 2 +
              2 * ‖realize gap omega x‖ ^ 2) := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => by positivity) hrhsInt ?_
      refine (ae_restrict_iff' (measurableSet_cubeSet Q)).2 ?_
      filter_upwards with x hx
      let A := HilbertVec.ofVec
        (stationaryLocalStreamApprox Q L S D omega x)
      let DX := realize D omega x
      let JX := realize J omega x
      have htri : ‖A - JX‖ ≤ ‖A - DX‖ + ‖DX - JX‖ := by
        simpa only [dist_eq_norm] using! dist_triangle A DX JX
      have hexact := norm_sq_stationaryLocalStreamApprox_sub_le
        Q L S D omega hx
      have hgapEq : DX - JX = realize gap omega x := by rfl
      have htri' :
          ‖HilbertVec.ofVec
              (stationaryLocalStreamApprox Q L S D omega x) -
            realize J omega x‖ ≤
          ‖HilbertVec.ofVec
              (stationaryLocalStreamApprox Q L S D omega x) -
            realize D omega x‖ + ‖realize gap omega x‖ := by
        simpa only [A, DX, JX, hgapEq] using! htri
      have hexact' : ‖A - DX‖ ^ 2 ≤
          2 * B.indicator (fun y => ‖realize D omega y‖ ^ 2) x +
            2 * G ^ 2 * ‖realize S omega x‖ ^ 2 := by
        simpa only [A, DX, B, G] using! hexact
      change ‖A - JX‖ ^ 2 ≤
        4 * B.indicator (fun y => ‖realize D omega y‖ ^ 2) x +
          4 * G ^ 2 * ‖realize S omega x‖ ^ 2 +
          2 * ‖realize gap omega x‖ ^ 2
      nlinarith [htri', hexact', norm_nonneg (A - JX),
        norm_nonneg (A - DX), norm_nonneg (realize gap omega x),
        sq_nonneg (‖A - DX‖ - ‖realize gap omega x‖)]
    refine hinner.trans (le_of_eq ?_)
    calc
      (∫ x in cubeSet Q,
        (4 * B.indicator (fun y => ‖realize D omega y‖ ^ 2) x +
          4 * G ^ 2 * ‖realize S omega x‖ ^ 2) +
          2 * ‖realize gap omega x‖ ^ 2) =
          (∫ x in cubeSet Q,
            4 * B.indicator (fun y => ‖realize D omega y‖ ^ 2) x +
              4 * G ^ 2 * ‖realize S omega x‖ ^ 2) +
            ∫ x in cubeSet Q, 2 * ‖realize gap omega x‖ ^ 2 :=
        integral_add
          ((hindint.const_mul 4).add (hSQint.const_mul (4 * G ^ 2)))
          (hgapQint.const_mul 2)
      _ = ((∫ x in cubeSet Q,
            4 * B.indicator (fun y => ‖realize D omega y‖ ^ 2) x) +
          ∫ x in cubeSet Q, 4 * G ^ 2 * ‖realize S omega x‖ ^ 2) +
          ∫ x in cubeSet Q, 2 * ‖realize gap omega x‖ ^ 2 := by
        rw [integral_add (hindint.const_mul 4)
          (hSQint.const_mul (4 * G ^ 2))]
      _ = (4 * (∫ x in B, ‖realize D omega x‖ ^ 2) +
          4 * G ^ 2 * (∫ x in cubeSet Q, ‖realize S omega x‖ ^ 2)) +
          2 * (∫ x in cubeSet Q, ‖realize gap omega x‖ ^ 2) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          setIntegral_indicator hBmeas,
          Set.inter_eq_self_of_subset_right
            (stationaryPotentialBoundaryStrip_subset_cubeSet Q L)]
  have hV : 0 < V := cubeVolume_pos Q
  have hscaled := mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hV.le)
  have hvalues :
      (∫ omega, ((4 * (∫ x in B, ‖realize D omega x‖ ^ 2) +
        4 * G ^ 2 * (∫ x in cubeSet Q, ‖realize S omega x‖ ^ 2)) +
        2 * (∫ x in cubeSet Q, ‖realize gap omega x‖ ^ 2))
        ∂M.P.toMeasure) =
      4 * (volume B).toReal * (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure) +
        4 * G ^ 2 * (V * ∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure) +
        2 * (V * ∫ omega, ‖gap omega‖ ^ 2 ∂M.P.toMeasure) := by
    calc
      (∫ omega,
        (4 * (∫ x in B, ‖realize D omega x‖ ^ 2) +
          4 * G ^ 2 * (∫ x in cubeSet Q, ‖realize S omega x‖ ^ 2)) +
          2 * (∫ x in cubeSet Q, ‖realize gap omega x‖ ^ 2)
        ∂M.P.toMeasure) =
          (∫ omega, 4 * (∫ x in B, ‖realize D omega x‖ ^ 2) +
            4 * G ^ 2 * (∫ x in cubeSet Q, ‖realize S omega x‖ ^ 2)
            ∂M.P.toMeasure) +
          ∫ omega, 2 * (∫ x in cubeSet Q, ‖realize gap omega x‖ ^ 2)
            ∂M.P.toMeasure :=
        integral_add
          (((integrable_setIntegral_normSq_realize M hBfin hDm hD).const_mul 4).add
            ((integrable_setIntegral_normSq_realize M hQfin hSm hS).const_mul
              (4 * G ^ 2)))
          ((integrable_setIntegral_normSq_realize M hQfin hgapm hgap).const_mul 2)
      _ = ((∫ omega, 4 * (∫ x in B, ‖realize D omega x‖ ^ 2)
            ∂M.P.toMeasure) +
          ∫ omega, 4 * G ^ 2 *
            (∫ x in cubeSet Q, ‖realize S omega x‖ ^ 2)
            ∂M.P.toMeasure) +
          ∫ omega, 2 * (∫ x in cubeSet Q, ‖realize gap omega x‖ ^ 2)
            ∂M.P.toMeasure := by
        rw [integral_add
          ((integrable_setIntegral_normSq_realize M hBfin hDm hD).const_mul 4)
          ((integrable_setIntegral_normSq_realize M hQfin hSm hS).const_mul
            (4 * G ^ 2))]
      _ = 4 * (volume B).toReal *
            (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure) +
          4 * G ^ 2 * (V * ∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure) +
          2 * (V * ∫ omega, ‖gap omega‖ ^ 2 ∂M.P.toMeasure) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          integral_setIntegral_normSq_realize M hBfin hDm hD,
          integral_setIntegral_normSq_realize M hQfin hSm hS,
          integral_setIntegral_normSq_realize M hQfin hgapm hgap,
          volume_cubeSet_toReal]
        dsimp only [B, V]
        ring
  rw [hvalues] at hscaled
  have hstrip := volume_stationaryPotentialBoundaryStrip_toReal_le Q L
  have hDnorm : 0 ≤ ∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure :=
    integral_nonneg fun _ => by positivity
  change V⁻¹ * _ ≤ _
  change _ ≤ 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * _ +
      2 * G ^ 2 * _) + 2 * ∫ omega, ‖gap omega‖ ^ 2 ∂M.P.toMeasure
  have hstripScaled :
      V⁻¹ * (4 * (volume B).toReal *
          (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure)) ≤
        2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
          (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure)) := by
    have hbase : 4 * (volume B).toReal ≤
        2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * V) := by
      calc
        4 * (volume B).toReal ≤
            4 * (((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ))) / 2 * V) :=
          mul_le_mul_of_nonneg_left (by simpa only [B, V] using! hstrip)
            (by norm_num)
        _ = 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * V) := by ring
    have hmul := mul_le_mul_of_nonneg_right hbase hDnorm
    calc
      V⁻¹ * (4 * (volume B).toReal *
          (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure)) ≤
          V⁻¹ * (2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * V) *
            (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure)) :=
        mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hV.le)
      _ = 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
          (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure)) := by field_simp
  calc
    V⁻¹ * _ ≤ V⁻¹ *
        (4 * (volume B).toReal * (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure) +
          4 * G ^ 2 * (V * ∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure) +
          2 * (V * ∫ omega, ‖gap omega‖ ^ 2 ∂M.P.toMeasure)) := hscaled
    _ = V⁻¹ * (4 * (volume B).toReal *
          (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure)) +
        4 * G ^ 2 * (∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure) +
        2 * ∫ omega, ‖gap omega‖ ^ 2 ∂M.P.toMeasure := by field_simp
    _ ≤ 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
          (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure)) +
        4 * G ^ 2 * (∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure) +
        2 * ∫ omega, ‖gap omega‖ ^ 2 ∂M.P.toMeasure :=
      by linarith only [hstripScaled]
    _ = 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
          (∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure) +
        2 * G ^ 2 * (∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure)) +
        2 * ∫ omega, ‖gap omega‖ ^ 2 ∂M.P.toMeasure := by ring

/-- The one-step solenoidal remainder admits an explicit smooth
antisymmetric stationary stream whose divergence field is arbitrarily close
in stationary `L²`. -/
theorem exists_oneStepSolenoidalApproximateStream
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (hh : 0 < h)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let R := oneStepOriginForcingL2 M n h p hh -
      oneStepPotentialProjection M n h p hh
    ∃ S : _root_.SubdiffusiveProcess.Model.PotentialSample d → Fin d → HilbertVec d,
      ∃ D : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d,
        StronglyMeasurable S ∧ MemLp S 2 M.P.toMeasure ∧
        (∀ᵐ omega ∂M.P.toMeasure, ∀ i m : Fin d,
          ContDiff ℝ (⊤ : ℕ∞)
            (stationaryStreamRealization S omega i m)) ∧
        (∀ omega, ∀ i m : Fin d,
          stationaryStreamRealization S omega m i =
            -stationaryStreamRealization S omega i m) ∧
        (∀ᵐ omega ∂M.P.toMeasure, ∀ x : Vec d,
          streamDivergence (stationaryStreamRealization S omega) x =
            (realize D omega x).toVec) ∧
        StronglyMeasurable D ∧
        ∃ hD : MemLp D 2 M.P.toMeasure,
          ‖hD.toLp D - R‖ < epsilon := by
  let := potentialSequenceVAddInvariant M
  let R := oneStepOriginForcingL2 M n h p hh -
    oneStepPotentialProjection M n h p hh
  have hRcont : Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z R) :=
    continuous_koopman_oneStepSolenoidalRemainder M n h p hh
  have hRsol : R ∈ Stationary.stationarySolenoidalSubspace
      (mu := M.P.toMeasure) (d := d) :=
    oneStepOriginForcingL2_sub_projection_mem_stationarySolenoidalSubspace
      M n h p hh
  have hepsHalf : 0 < epsilon / 2 := div_pos hepsilon (by norm_num)
  obtain ⟨s, hs, hlarge⟩ :=
    exists_streamProduct_scale_norm_mollifyL2_oneStepSolenoidalRemainder_lt
      M n h p hh hepsHalf
  obtain ⟨r, hr, hsmall⟩ :=
    exists_streamProduct_radius_norm_mollifyL2_sub_lt
      M R hRcont hepsHalf
  obtain ⟨S, D, hSm, hS, hSmooth, hAnti, hDiv, hDm, hD, hDae⟩ :=
    exists_twoScaleStationaryKernelStream M hr hs R hRcont hRsol
  refine ⟨S, D, hSm, hS, hSmooth, hAnti, hDiv, hDm, hD, ?_⟩
  let X := stationaryVectorRepresentative M R
  let nu : Vec d → ℝ := fun x =>
    streamProductDensity d hr x - streamProductDensity d hs x
  let psi : Fin d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun i =>
    representativeMollify nu (representativeCoord X i)
  have hnu : Continuous nu :=
    (continuous_streamProductDensity d hr).sub
      (continuous_streamProductDensity d hs)
  have hnuc : HasCompactSupport nu :=
    (hasCompactSupport_streamProductDensity d hr).sub
      (hasCompactSupport_streamProductDensity d hs)
  let hpsiM : ∀ i, StronglyMeasurable (psi i) := fun i =>
    stronglyMeasurable_representativeMollify hnu
      (stronglyMeasurable_representativeCoord
        (stronglyMeasurable_stationaryVectorRepresentative M R) i)
  let hpsi : ∀ i, MemLp (psi i) 2 M.P.toMeasure := fun i =>
    memLp_two_representativeMollify M hnu
      (hnu.integrable_of_hasCompactSupport hnuc)
      (stronglyMeasurable_representativeCoord
        (stronglyMeasurable_stationaryVectorRepresentative M R) i)
      (memLp_representativeCoord M
        (stronglyMeasurable_stationaryVectorRepresentative M R)
        (memLp_two_stationaryVectorRepresentative M R) i)
  let hpack := memLp_two_streamVectorPack M hpsiM hpsi
  have hDae' : D =ᵐ[M.P.toMeasure] streamVectorPack psi := by
    simpa only [psi, nu, X] using! hDae
  have hclass : hD.toLp D =
      Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hr) R -
        Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hs) R := by
    calc
      hD.toLp D = hpack.toLp (streamVectorPack psi) :=
        MemLp.toLp_congr hD hpack hDae'
      _ = Stationary.mollifyL2 (mu := M.P.toMeasure) nu R := by
        exact toLp_streamVectorPack_representativeMollify_eq_mollifyL2
          M hnu hnuc R hRcont
      _ = Stationary.mollifyL2 (mu := M.P.toMeasure)
            (streamProductDensity d hr) R -
          Stationary.mollifyL2 (mu := M.P.toMeasure)
            (streamProductDensity d hs) R := by
        exact Stationary.mollifyL2_kernel_sub_of_continuous
          (continuous_streamProductDensity d hr)
          (hasCompactSupport_streamProductDensity d hr)
          (continuous_streamProductDensity d hs)
          (hasCompactSupport_streamProductDensity d hs) R hRcont
  rw [hclass]
  calc
    ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hr) R -
        Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hs) R - R‖ =
        ‖(Stationary.mollifyL2 (mu := M.P.toMeasure)
            (streamProductDensity d hr) R - R) -
          Stationary.mollifyL2 (mu := M.P.toMeasure)
            (streamProductDensity d hs) R‖ := by
      congr 1
      abel
    _ ≤ ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
            (streamProductDensity d hr) R - R‖ +
          ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
            (streamProductDensity d hs) R‖ := norm_sub_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hsmall hlarge
    _ = epsilon := by ring

/-- Thermodynamic zero-normal approximation of the one-step solenoidal
remainder.  At fixed strip depth `L`, the only cube-dependent price tends to
zero; the boundary price has the printed `3⁻ᴸ` scaling and the auxiliary
stream-divergence gap is absorbed into the arbitrary tolerance `eta`. -/
theorem exists_oneStepSolenoidalZeroNormal_family_bound
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (hh : 0 < h)
    (L : ℕ) {eta : ℝ} (heta : 0 < eta) :
    let R := oneStepOriginForcingL2 M n h p hh -
      oneStepPotentialProjection M n h p hh
    ∃ (V : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → Vec d) (g : ℕ → ℝ),
      (∀ K, 0 ≤ g K) ∧
      Filter.Tendsto g Filter.atTop (nhds 0) ∧
      (∀ K : ℕ, ∀ᵐ omega ∂M.P.toMeasure,
        IsSolenoidalZeroNormalTraceOn
          (openCubeSet (originCube d (K : ℤ))) (V K omega)) ∧
      (∀ K : ℕ, Integrable (fun omega =>
        ∫ x in cubeSet (originCube d (K : ℤ)),
          ‖HilbertVec.ofVec (V K omega x) -
            realize (stationaryVectorRepresentative M R) omega x‖ ^ 2)
          M.P.toMeasure) ∧
      (∀ K : ℕ, ∀ᵐ omega ∂M.P.toMeasure,
        MemLp (fun x =>
          HilbertVec.ofVec (V K omega x) -
            realize (stationaryVectorRepresentative M R) omega x)
          2 (volume.restrict (cubeSet (originCube d (K : ℤ))))) ∧
      ∀ K : ℕ,
        (cubeVolume (originCube d (K : ℤ)))⁻¹ *
            (∫ omega, (∫ x in cubeSet (originCube d (K : ℤ)),
              ‖HilbertVec.ofVec (V K omega x) -
                realize (stationaryVectorRepresentative M R) omega x‖ ^ 2)
              ∂M.P.toMeasure) ≤
          2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (‖R‖ + 1) ^ 2) +
            eta + g K := by
  let := potentialSequenceVAddInvariant M
  let R := oneStepOriginForcingL2 M n h p hh -
    oneStepPotentialProjection M n h p hh
  let eps : ℝ := min 1 (Real.sqrt (eta / 2))
  have heps : 0 < eps := lt_min one_pos (Real.sqrt_pos.2 (by positivity))
  have heps1 : eps ≤ 1 := min_le_left _ _
  have hepsSq : 2 * eps ^ 2 ≤ eta := by
    have hepsSqrt : eps ≤ Real.sqrt (eta / 2) := min_le_right _ _
    have heps0 : 0 ≤ eps := heps.le
    have hsqrt0 : 0 ≤ Real.sqrt (eta / 2) := Real.sqrt_nonneg _
    have hsquare : eps ^ 2 ≤ (Real.sqrt (eta / 2)) ^ 2 :=
      pow_le_pow_left₀ heps0 hepsSqrt 2
    rw [Real.sq_sqrt (by positivity)] at hsquare
    linarith
  obtain ⟨S, D, hSm, hS, hSmooth, hAnti, hDiv, hDm, hD, hclose⟩ :=
    exists_oneStepSolenoidalApproximateStream M n h p hh heps
  let J : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d := stationaryVectorRepresentative M R
  let hJm : StronglyMeasurable J :=
    stronglyMeasurable_stationaryVectorRepresentative M R
  let hJ : MemLp J 2 M.P.toMeasure :=
    memLp_two_stationaryVectorRepresentative M R
  have hJclass : hJ.toLp J = R :=
    toLp_stationaryVectorRepresentative M R
  let ID : ℝ := ∫ omega, ‖D omega‖ ^ 2 ∂M.P.toMeasure
  let IS : ℝ := ∫ omega, ‖S omega‖ ^ 2 ∂M.P.toMeasure
  let E : ℝ := ∫ omega, ‖D omega - J omega‖ ^ 2 ∂M.P.toMeasure
  have hDE : E = ‖hD.toLp D - R‖ ^ 2 := by
    dsimp only [E]
    rw [integral_normSq_sub_eq_norm_sq_toLp hD hJ, hJclass]
  have hE : 2 * E ≤ eta := by
    rw [hDE]
    have hnorm0 : 0 ≤ ‖hD.toLp D - R‖ := norm_nonneg _
    have hsq : ‖hD.toLp D - R‖ ^ 2 ≤ eps ^ 2 := by
      nlinarith
    linarith
  have hDnorm : ‖hD.toLp D‖ ≤ ‖R‖ + 1 := by
    calc
      ‖hD.toLp D‖ = ‖(hD.toLp D - R) + R‖ := by congr 1; abel
      _ ≤ ‖hD.toLp D - R‖ + ‖R‖ := norm_add_le _ _
      _ ≤ ‖R‖ + 1 := by linarith
  have hID : ID ≤ (‖R‖ + 1) ^ 2 := by
    rw [show ID = ‖hD.toLp D‖ ^ 2 by
      exact integral_normSq_eq_norm_sq_toLp hD]
    exact pow_le_pow_left₀ (norm_nonneg _) hDnorm 2
  let V : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → Vec d := fun K omega =>
    stationaryLocalStreamApprox (originCube d (K : ℤ)) L S D omega
  let g : ℕ → ℝ := fun K =>
    4 * stationaryPotentialCutoffGradBound
      (originCube d (K : ℤ)) L ^ 2 * IS
  refine ⟨V, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K
    dsimp only [g, IS]
    positivity
  · have ht := tendsto_stationaryPotentialCutoffPrimitivePrice_originCube
      d L IS
    have ht2 := ht.const_mul 2
    convert ht2 using 1
    · funext K
      dsimp only [g]
      ring
    · simp
  · intro K
    filter_upwards [hSmooth, hDiv] with omega hsmooth hdiv
    dsimp only [V]
    exact isSolenoidalZeroNormalTraceOn_stationaryLocalStreamApprox
      (originCube d (K : ℤ)) L hsmooth (hAnti omega) hdiv
  · intro K
    exact integrable_setIntegral_normSq_stationaryLocalStreamApprox_target
      M (originCube d (K : ℤ)) L hSm hS hDm hD hJm hJ
  · intro K
    exact ae_memLp_two_stationaryLocalStreamApprox_sub_target
      M (originCube d (K : ℤ)) L hSm hS hDm hD hJm hJ
  · intro K
    have hkey :=
      normalized_integral_setIntegral_normSq_stationaryLocalStreamApprox_target_le
        M (originCube d (K : ℤ)) L hSm hS hDm hD hJm hJ
    have hscale : 0 ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) := by positivity
    have hscaleID := mul_le_mul_of_nonneg_left hID hscale
    change _ ≤ 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
        (‖R‖ + 1) ^ 2) + eta + g K
    calc
      _ ≤ 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * ID +
          2 * stationaryPotentialCutoffGradBound
            (originCube d (K : ℤ)) L ^ 2 * IS) + 2 * E := by
        simpa only [V, J, ID, IS, E] using! hkey
      _ = 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * ID) +
          g K + 2 * E := by
        dsimp only [g]
        ring
      _ ≤ 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
          (‖R‖ + 1) ^ 2) + g K + eta := by
        linarith
      _ = 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
          (‖R‖ + 1) ^ 2) + eta + g K := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
