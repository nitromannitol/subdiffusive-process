module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCombinedSignedFiniteHeight

@[expose] public section

/-!
# Signed combined-pairing radius step

This file connects the finite-height combined pairing to the localized signed
weak-energy identity.  It keeps the residual, affine lift, and residual datum
profiles separate after the descendant sum.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Linearity of the cross-scale profile for the exact energy combination
produced by the combined signed finite-height cap. -/
theorem boundaryCrossScaleEnergyProfile_combined_three_eq
    (Q R : TriadicCube d) (center : Vec d) (rho : ℝ)
    (Er Ev Eh : Vec d → ℝ)
    (hr : IntegrableOn Er (openCubeSet Q))
    (hv : IntegrableOn Ev (openCubeSet Q))
    (hh : IntegrableOn Eh (openCubeSet Q)) :
    boundaryCrossScaleEnergyProfile Q R center rho
        (fun x ↦ Er x + 2 * Ev x + (1 / 2 : ℝ) * Eh x) =
      boundaryCrossScaleEnergyProfile Q R center rho Er +
        2 * boundaryCrossScaleEnergyProfile Q R center rho Ev +
        (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rho Eh := by
  let P := coarseCaccioppoliLocalClosedCube R center rho
  have hPm : MeasurableSet P :=
    measurableSet_coarseCaccioppoliLocalClosedCube R center rho
  have hrP : IntegrableOn (P.indicator Er) (openCubeSet Q) := hr.indicator hPm
  have hvP : IntegrableOn (P.indicator Ev) (openCubeSet Q) := hv.indicator hPm
  have hhP : IntegrableOn (P.indicator Eh) (openCubeSet Q) := hh.indicator hPm
  have hvScaled : IntegrableOn ((2 : ℝ) • P.indicator Ev) (openCubeSet Q) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hvP.const_mul 2
  have hhScaled : IntegrableOn ((1 / 2 : ℝ) • P.indicator Eh)
      (openCubeSet Q) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hhP.const_mul (1 / 2 : ℝ)
  have hfun : P.indicator (fun x ↦ Er x + 2 * Ev x + (1 / 2 : ℝ) * Eh x) =
      fun x ↦ (P.indicator Er) x + 2 * (P.indicator Ev) x +
        (1 / 2 : ℝ) * (P.indicator Eh) x := by
    funext x
    by_cases hx : x ∈ P <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  unfold boundaryCrossScaleEnergyProfile
  rw [show coarseCaccioppoliLocalClosedCube R center rho = P by rfl, hfun]
  change volumeAverage (openCubeSet Q)
      (((P.indicator Er) + (2 : ℝ) • (P.indicator Ev)) +
        (1 / 2 : ℝ) • (P.indicator Eh)) = _
  calc
    _ = volumeAverage (openCubeSet Q)
          ((P.indicator Er) + (2 : ℝ) • (P.indicator Ev)) +
        volumeAverage (openCubeSet Q) ((1 / 2 : ℝ) • (P.indicator Eh)) :=
      volumeAverage_add (hrP.add hvScaled) hhScaled
    _ = _ := by
      rw [volumeAverage_add hrP hvScaled,
        volumeAverage_smul, volumeAverage_smul]

omit [NeZero d] in
/-- One signed combined-pairing step.  Its outer coefficients are the exact
ones obtained by adding the signed weak-energy row and the finite-height cap;
no affine correction norm or inverse fractional power is introduced. -/
theorem boundaryCrossScale_physical_le_of_combinedSignedPairing
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u r v hRes : H1Function (openCubeSet Q))
    (g : Vec d → Vec d) (center : Vec d) {rhoInner rhoOuter P Ag : ℝ}
    (hgrad : ∀ x, u.grad x = r.grad x + v.grad x)
    (hweakR : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) r g)
    (hweakV : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube Q center 1)
      (fun x ↦ r.toFun x - hRes.toFun x))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter) (houter : rhoOuter < 1)
    (hforce : volumeAverage (openCubeSet Q)
      (boundaryCoerciveForceDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g) ≤ Ag)
    (hpair : |volumeAverage (openCubeSet Q)
      (boundaryCorrectedFluxCutoffPairingDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
        (r - hRes).toFun (r + (2 : ℝ) • v).grad g)| ≤
      (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
        (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (r.grad x) +
          2 * (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)) +
          (1 / 2 : ℝ) *
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (hRes.grad x))) + P) :
    boundaryCrossScaleEnergyProfile Q Q center rhoInner (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (r.grad x)) +
        (5 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)) +
        (29 / 8 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (hRes.grad x)) +
        (5 / 2 : ℝ) * Ag + P := by
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  have hbetween := coarseCaccioppoliBufferedCutoffRadius_between hlt
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta :=
    coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hbetween.1
  have hetaCompact : HasCompactSupport eta :=
    coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner hbetween.1
  have hetaSupport : tsupport eta ⊆ coarseCaccioppoliLocalOpenCube Q center 1 :=
    (coarseCaccioppoliLocalCanonicalFun_tsupport_subset_localClosedCube
      hinner hbetween.1).trans
      (coarseCaccioppoliLocalClosedCube_subset_localOpenCube_one_of_lt_one
        (hbetween.2.trans houter))
  have hsigned := volumeAverage_localizedSignedAffineResidualEnergy_le
    M L omega Q u r v hRes g hgrad hweakR hweakV hg hzero
      heta hetaCompact hetaSupport
  let Er : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (r.grad x)
  let Ev : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)
  let Eh : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (hRes.grad x)
  have huInt := integrableOn_aCutoff_energy M L omega Q u
  have hrInt := integrableOn_aCutoff_energy M L omega Q r
  have hvInt := integrableOn_aCutoff_energy M L omega Q v
  have hhInt := integrableOn_aCutoff_energy M L omega Q hRes
  have hmainU : IntegrableOn (boundaryCoerciveMainDensity
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta u.grad) (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega u.grad_memVectorL2
        heta hetaCompact
  have hmainR : IntegrableOn (boundaryCoerciveMainDensity
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta r.grad) (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega r.grad_memVectorL2
        heta hetaCompact
  have hmainV : IntegrableOn (boundaryCoerciveMainDensity
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta v.grad) (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega v.grad_memVectorL2
        heta hetaCompact
  have hmainH : IntegrableOn (boundaryCoerciveMainDensity
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta hRes.grad) (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega hRes.grad_memVectorL2
        heta hetaCompact
  let pairR : Vec d → ℝ := boundaryCorrectedFluxCutoffPairingDensity
    (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
    (r - hRes).toFun r.grad g
  let pairV : Vec d → ℝ := boundaryCorrectedFluxCutoffPairingDensity
    (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
    (r - hRes).toFun v.grad (fun _ ↦ 0)
  let pairC : Vec d → ℝ := boundaryCorrectedFluxCutoffPairingDensity
    (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
    (r - hRes).toFun (r + (2 : ℝ) • v).grad g
  have hpairRInt : IntegrableOn pairR (openCubeSet Q) := by
    simpa only [pairR, H1Function.sub_toFun] using!
      integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
        M L omega r hRes hg heta hetaCompact
  have hpairVInt : IntegrableOn pairV (openCubeSet Q) := by
    have hflux := memVectorL2_aCutoff_smul_grad M L omega Q v
    have htest :=
      memVectorL2_sub_mul_scalarCutoffGradientField_sq r hRes heta hetaCompact
    have hraw := integrableOn_vecDot_of_memVectorL2 hflux htest
    dsimp only [pairV]
    apply hraw.congr_fun
    · intro x _hx
      simp only [boundaryCorrectedFluxCutoffPairingDensity,
        boundaryCorrectedFlux, add_zero, H1Function.sub_toFun]
    · exact measurableSet_openCubeSet Q
  have hpairFun : pairR + (2 : ℝ) • pairV = pairC := by
    funext x
    simpa only [pairR, pairV, pairC, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      H1Function.add_grad, H1Function.smul_grad] using!
      boundaryCorrectedFluxCutoffPairingDensity_residual_add_two_lift
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta (r - hRes).toFun
          r.grad v.grad g x
  have hpairEq : volumeAverage (openCubeSet Q) pairR +
      2 * volumeAverage (openCubeSet Q) pairV =
      volumeAverage (openCubeSet Q) pairC := by
    rw [← volumeAverage_smul]
    rw [← volumeAverage_add hpairRInt (by
      simpa only [Pi.smul_apply, smul_eq_mul] using! hpairVInt.const_mul 2)]
    exact volumeAverage_eq_of_ae_eq (Filter.Eventually.of_forall fun x ↦
      congrFun hpairFun x)
  have hinnerU := boundaryCrossScaleEnergyProfile_le_boundaryCoerciveMain
    hinner hbetween.1
    (fun x _ ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le)
    huInt hmainU
  have houterR := volumeAverage_boundaryCoerciveMain_localCanonicalFun_le_outerProfile
    hinner hbetween.1
    (fun x _ ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le)
    hrInt hmainR
  have houterV := volumeAverage_boundaryCoerciveMain_localCanonicalFun_le_outerProfile
    hinner hbetween.1
    (fun x _ ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le)
    hvInt hmainV
  have houterH := volumeAverage_boundaryCoerciveMain_localCanonicalFun_le_outerProfile
    hinner hbetween.1
    (fun x _ ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le)
    hhInt hmainH
  have hmonoR := boundaryCrossScaleEnergyProfile_mono
    (Q := Q) (R := Q) (center := center) hbetween.2.le
    (fun x _ ↦ mul_nonneg
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le (vecNormSq_nonneg _))
    hrInt
  have hmonoV := boundaryCrossScaleEnergyProfile_mono
    (Q := Q) (R := Q) (center := center) hbetween.2.le
    (fun x _ ↦ mul_nonneg
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le (vecNormSq_nonneg _))
    hvInt
  have hmonoH := boundaryCrossScaleEnergyProfile_mono
    (Q := Q) (R := Q) (center := center) hbetween.2.le
    (fun x _ ↦ mul_nonneg
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le (vecNormSq_nonneg _))
    hhInt
  have houterR' := houterR.trans hmonoR
  have houterV' := houterV.trans hmonoV
  have houterH' := houterH.trans hmonoH
  have houterHDatum : volumeAverage (openCubeSet Q)
      (boundaryCoerciveDatumDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta hRes.grad) ≤
      boundaryCrossScaleEnergyProfile Q Q center rhoOuter Eh := by
    simpa only [boundaryCoerciveDatumDensity, boundaryCoerciveMainDensity] using!
      houterH'
  have hpairNeg : -volumeAverage (openCubeSet Q)
      (boundaryCorrectedFluxCutoffPairingDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
        (r - hRes).toFun (r + (2 : ℝ) • v).grad g) ≤
      |volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
          (r - hRes).toFun (r + (2 : ℝ) • v).grad g)| := neg_le_abs _
  have hpairSplit := boundaryCrossScaleEnergyProfile_combined_three_eq
    Q Q center rhoOuter Er Ev Eh
      (by simpa only [Er] using! hrInt)
      (by simpa only [Ev] using! hvInt)
      (by simpa only [Eh] using! hhInt)
  dsimp only [eta, Er, Ev, Eh, pairR, pairV, pairC, H1Function.sub_toFun] at hsigned hinnerU houterR' houterV' houterH' houterHDatum hpairEq hpairNeg hpairSplit hpair hforce ⊢
  simp only [H1Function.sub_toFun] at hpairEq hpairNeg hpair
  rw [hpairSplit] at hpair
  linarith only [hsigned, hinnerU, houterR', houterV', houterHDatum,
    hpairEq, hpairNeg, hpair, hforce]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
