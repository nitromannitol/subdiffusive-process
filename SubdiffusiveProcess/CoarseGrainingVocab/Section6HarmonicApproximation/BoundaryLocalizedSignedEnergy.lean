module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryLocalizedHalfSteps

@[expose] public section

/-!
# Signed localized boundary energy

The cutoff-product term must retain its sign until after affine covariance is
applied.  This file records the direct weak test in that form.  In particular,
the sign below comes from testing the weak equation by the localized function
`eta ^ 2 * (u - h)`; it is not inferred from an absolute-value estimate.

PROVENANCE: this is the signed form of the boundary-energy assembly used in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryAssemblyEnergy.lean`, with
the localized trace carrier supplied by `BoundaryLocalizedCoerciveTest.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open Homogenization.WeakPoissonEquationOn

noncomputable section

variable {d : ℕ}

/-- Generic signed integration step.  The corrected-flux pairing stays on the
left, exactly as produced by the localized weak test. -/
theorem setIntegral_boundaryCoerciveMain_add_correctedFluxPairing_le_of_weak_identity
    {Q : TriadicCube d} {a eta : Vec d → ℝ}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (ha : ∀ x ∈ openCubeSet Q, 0 < a x)
    (hmain : IntegrableOn (boundaryCoerciveMainDensity a eta u.grad)
      (openCubeSet Q))
    (hweakLeft : IntegrableOn
      (boundaryCoerciveWeakLeftDensity a eta
        (fun y => u.toFun y - h.toFun y) u.grad h.grad) (openCubeSet Q))
    (hweakForce : IntegrableOn
      (boundaryCoerciveWeakForceDensity eta
        (fun y => u.toFun y - h.toFun y) u.grad h.grad g) (openCubeSet Q))
    (hrhs : IntegrableOn
      (boundaryCoerciveRhsDensity a eta
        (fun y => u.toFun y - h.toFun y) u.grad h.grad g) (openCubeSet Q))
    (hdatum : IntegrableOn (boundaryCoerciveDatumDensity a eta h.grad)
      (openCubeSet Q))
    (hforce : IntegrableOn (boundaryCoerciveForceDensity a eta g)
      (openCubeSet Q))
    (hpair : IntegrableOn
      (boundaryCorrectedFluxCutoffPairingDensity a eta
        (fun y => u.toFun y - h.toFun y) u.grad g) (openCubeSet Q))
    (hweak :
      ∫ x in openCubeSet Q,
          boundaryCoerciveWeakLeftDensity a eta
            (fun y => u.toFun y - h.toFun y) u.grad h.grad x ∂volume =
        -∫ x in openCubeSet Q,
          boundaryCoerciveWeakForceDensity eta
            (fun y => u.toFun y - h.toFun y) u.grad h.grad g x ∂volume) :
    (∫ x in openCubeSet Q,
        boundaryCoerciveMainDensity a eta u.grad x ∂volume) +
      ∫ x in openCubeSet Q,
        boundaryCorrectedFluxCutoffPairingDensity a eta
          (fun y => u.toFun y - h.toFun y) u.grad g x ∂volume ≤
      (1 / 4 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveMainDensity a eta u.grad x ∂volume +
        (5 / 2 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveDatumDensity a eta h.grad x ∂volume +
        (5 / 2 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveForceDensity a eta g x ∂volume := by
  let w : Vec d → ℝ := fun y => u.toFun y - h.toFun y
  have hid := setIntegral_boundaryCoerciveMain_eq_rhs
    hmain hweakLeft hweakForce hrhs hweak
  have hsumInt : IntegrableOn (fun x =>
      boundaryCoerciveRhsDensity a eta w u.grad h.grad g x +
        boundaryCorrectedFluxCutoffPairingDensity a eta w u.grad g x)
      (openCubeSet Q) := hrhs.add hpair
  have hboundInt : IntegrableOn (fun x =>
      (1 / 4 : ℝ) * boundaryCoerciveMainDensity a eta u.grad x +
        (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta h.grad x +
        (5 / 2 : ℝ) * boundaryCoerciveForceDensity a eta g x)
      (openCubeSet Q) :=
    ((hmain.const_mul _).add (hdatum.const_mul _)).add (hforce.const_mul _)
  have hmono :
      ∫ x in openCubeSet Q,
          (boundaryCoerciveRhsDensity a eta w u.grad h.grad g x +
            boundaryCorrectedFluxCutoffPairingDensity a eta w u.grad g x) ∂volume ≤
        ∫ x in openCubeSet Q,
          ((1 / 4 : ℝ) * boundaryCoerciveMainDensity a eta u.grad x +
            (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta h.grad x +
            (5 / 2 : ℝ) * boundaryCoerciveForceDensity a eta g x) ∂volume := by
    apply integral_mono_ae hsumInt hboundInt
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact boundaryCoerciveRhsDensity_add_correctedFluxPairing_le heta (ha x hx)
  rw [integral_add hrhs hpair] at hmono
  have hboundEq :
      ∫ x in openCubeSet Q,
          ((1 / 4 : ℝ) * boundaryCoerciveMainDensity a eta u.grad x +
            (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta h.grad x +
            (5 / 2 : ℝ) * boundaryCoerciveForceDensity a eta g x) ∂volume =
        (1 / 4 : ℝ) * ∫ x in openCubeSet Q,
            boundaryCoerciveMainDensity a eta u.grad x ∂volume +
          (5 / 2 : ℝ) * ∫ x in openCubeSet Q,
            boundaryCoerciveDatumDensity a eta h.grad x ∂volume +
          (5 / 2 : ℝ) * ∫ x in openCubeSet Q,
            boundaryCoerciveForceDensity a eta g x ∂volume := by
    calc
      _ = (∫ x in openCubeSet Q,
              ((1 / 4 : ℝ) * boundaryCoerciveMainDensity a eta u.grad x +
                (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta h.grad x) ∂volume) +
            ∫ x in openCubeSet Q,
              (5 / 2 : ℝ) * boundaryCoerciveForceDensity a eta g x ∂volume := by
          simpa only [Pi.add_apply] using!
            (integral_add ((hmain.const_mul _).add (hdatum.const_mul _))
              (hforce.const_mul _))
      _ = ((∫ x in openCubeSet Q,
              (1 / 4 : ℝ) * boundaryCoerciveMainDensity a eta u.grad x ∂volume) +
            ∫ x in openCubeSet Q,
              (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta h.grad x ∂volume) +
            ∫ x in openCubeSet Q,
              (5 / 2 : ℝ) * boundaryCoerciveForceDensity a eta g x ∂volume := by
          congr 1
          simpa only [Pi.add_apply] using!
            (integral_add (hmain.const_mul _) (hdatum.const_mul _))
      _ = _ := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hboundEq] at hmono
  linarith only [hid, hmono]

/-- Localized-trace signed weak-energy inequality for the GMC cutoff. -/
theorem setIntegral_aCutoff_boundaryCoerciveMain_add_pair_le_of_localizedZeroTrace
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} {u h : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun y => u.toFun y - h.toFun y))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaSupport : tsupport eta ⊆ V) :
    (∫ x in openCubeSet Q,
        boundaryCoerciveMainDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad x ∂volume) +
      ∫ x in openCubeSet Q,
        boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          (fun y => u.toFun y - h.toFun y) u.grad g x ∂volume ≤
      (1 / 4 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad x ∂volume +
        (5 / 2 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta h.grad x ∂volume +
        (5 / 2 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g x ∂volume := by
  let a := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega
  let w : Vec d → ℝ := fun y => u.toFun y - h.toFun y
  have htest : MemVectorL2 (openCubeSet Q)
      (boundarySqCutoffTestGradient eta u h) :=
    memVectorL2_boundarySqCutoffTestGradient_of_smooth_compact u h heta hetaCompact
  have hmain : IntegrableOn (boundaryCoerciveMainDensity a eta u.grad)
      (openCubeSet Q) := by
    simpa only [a, boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega u.grad_memVectorL2
        heta hetaCompact
  have hdatum : IntegrableOn (boundaryCoerciveDatumDensity a eta h.grad)
      (openCubeSet Q) := by
    simpa only [a, boundaryCoerciveDatumDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega h.grad_memVectorL2
        heta hetaCompact
  have hforce : IntegrableOn (boundaryCoerciveForceDensity a eta g)
      (openCubeSet Q) := by
    simpa only [a] using!
      integrableOn_aCutoff_boundaryCoerciveForceDensity M L omega hg heta hetaCompact
  have hweakLeft : IntegrableOn
      (boundaryCoerciveWeakLeftDensity a eta w u.grad h.grad)
      (openCubeSet Q) := by
    have hp := integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q u) htest
    simpa only [a, boundaryCoerciveWeakLeftDensity,
      boundarySqCutoffTestGradient, w] using! hp
  have hweakForce : IntegrableOn
      (boundaryCoerciveWeakForceDensity eta w u.grad h.grad g)
      (openCubeSet Q) := by
    have hp := integrableOn_vecDot_of_memVectorL2 hg htest
    simpa only [boundaryCoerciveWeakForceDensity,
      boundarySqCutoffTestGradient, w] using! hp
  have hrhs : IntegrableOn
      (boundaryCoerciveRhsDensity a eta w u.grad h.grad g)
      (openCubeSet Q) := by
    have hsum : IntegrableOn (fun x =>
        boundaryCoerciveMainDensity a eta u.grad x -
          boundaryCoerciveWeakLeftDensity a eta w u.grad h.grad x -
          boundaryCoerciveWeakForceDensity eta w u.grad h.grad g x)
        (openCubeSet Q) := (hmain.sub hweakLeft).sub hweakForce
    apply hsum.congr_fun
    · intro x _
      have hleft := boundaryCoercive_main_sub_weakLeft
        a eta w u.grad h.grad x
      have hright := boundaryCoercive_rhs_add_weakForce
        a eta w u.grad h.grad g x
      linarith only [hleft, hright]
    · exact measurableSet_openCubeSet Q
  have hpair : IntegrableOn
      (boundaryCorrectedFluxCutoffPairingDensity a eta w u.grad g)
      (openCubeSet Q) := by
    simpa only [a, w] using!
      integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
        M L omega u h hg heta hetaCompact
  have hweakIdentity :=
    setIntegral_boundarySqCutoffTestGradient_identity_of_localizedZeroTrace
      hweak hzero heta hetaCompact hetaSupport
  apply
    setIntegral_boundaryCoerciveMain_add_correctedFluxPairing_le_of_weak_identity
      heta (fun x _ => SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x)
      hmain hweakLeft hweakForce hrhs hdatum hforce hpair
  simpa only [a, boundaryCoerciveWeakLeftDensity,
    boundaryCoerciveWeakForceDensity, boundarySqCutoffTestGradient, w] using!
      hweakIdentity

/-- Average form of the localized signed weak-energy inequality. -/
theorem volumeAverage_aCutoff_boundaryCoerciveMain_add_pair_le_of_localizedZeroTrace
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} {u h : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun y => u.toFun y - h.toFun y))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaSupport : tsupport eta ⊆ V) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveMainDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
      volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          (fun y => u.toFun y - h.toFun y) u.grad g) ≤
      (1 / 4 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
        (5 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta h.grad) +
        (5 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g) := by
  have hset :=
    setIntegral_aCutoff_boundaryCoerciveMain_add_pair_le_of_localizedZeroTrace
      M L omega hweak hg hzero heta hetaCompact hetaSupport
  have hc : 0 ≤ (volume (openCubeSet Q)).toReal⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  have hs := mul_le_mul_of_nonneg_left hset hc
  unfold volumeAverage
  nlinarith only [hs]

/-- The signed physical weak test after affine covariance.  The residual
pairing is introduced in the favorable direction before any absolute value
is taken. -/
theorem volumeAverage_physicalMain_add_residualPair_le_jointBudget
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u h v ell : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
    (hweakU : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g)
    (hweakRes : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) (u - v) g)
    (hweakV : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
    (hg : MemVectorL2 (openCubeSet Q) g)
    {V : Set (Vec d)}
    (hphysical : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ u.toFun x - h.toFun x))
    (haffine : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (Set.univ : Set (Vec d)) (fun x ↦ v.toFun x - ell.toFun x))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaSupport : tsupport eta ⊆ V) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveMainDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
      volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          (fun x ↦ (u - v).toFun x - (h - ell).toFun x)
          (u - v).grad g) ≤
      (1 / 4 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
        (5 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta h.grad) +
        (5 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g) +
        volumeAverage (openCubeSet Q) (fun x ↦
          eta x ^ 2 *
            (((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) / 2) *
                vecNormSq (u.grad x - h.grad x) +
              2 * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (h.grad x - ell.grad x) +
              2 * (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ *
                vecNormSq (g x) +
              (3 * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x / 2) *
                vecNormSq (v.grad x))) := by
  have hsigned :=
    volumeAverage_aCutoff_boundaryCoerciveMain_add_pair_le_of_localizedZeroTrace
      M L omega hweakU hg hphysical heta hetaCompact hetaSupport
  have hcov :=
    volumeAverage_residualCorrectedFluxPairing_le_physical_add_jointBudget
      M L omega Q u h v ell g hweakRes hweakV hg
        hphysical haffine heta hetaCompact hetaSupport
  linarith only [hsigned, hcov]

/-- Localized affine/residual energy split with the sign supplied by testing
the coefficient-harmonic lift against `eta^2 * (r - hRes)` itself.  No norm
bound on the correction `v - ell` occurs. -/
theorem volumeAverage_localizedAffineEnergySplit_identity
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u r v hRes : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = r.grad x + v.grad x)
    (hweakV : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ r.toFun x - hRes.toFun x))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaSupport : tsupport eta ⊆ V) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveMainDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
      2 * volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          (fun x ↦ r.toFun x - hRes.toFun x) v.grad (fun _ ↦ 0)) =
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad) +
        volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
        2 * volumeAverage (openCubeSet Q) (fun x ↦
          eta x ^ 2 * vecDot
            ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
            (hRes.grad x)) := by
  let hComp : H1Function (openCubeSet Q) := v - (r - hRes)
  have hzeroComp : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ v.toFun x - hComp.toFun x) := by
    exact Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun x ↦ by simp [hComp]) hzero
  have hzeroL2 : MemVectorL2 (openCubeSet Q)
      (fun _ : Vec d ↦ (0 : Vec d)) := by
    simp [MemVectorL2, volumeMeasureOn]
  have hpairRaw := volumeAverage_boundaryCorrectedFluxCutoffPairing_eq_neg_bulk
    M L omega Q v hComp (fun _ ↦ 0) hweakV hzeroL2 hzeroComp
      heta hetaCompact hetaSupport
  have hpair : volumeAverage (openCubeSet Q)
      (boundaryCorrectedFluxCutoffPairingDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
        (fun x ↦ r.toFun x - hRes.toFun x) v.grad (fun _ ↦ 0)) =
      -volumeAverage (openCubeSet Q) (fun x ↦
        eta x ^ 2 * vecDot
          ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
          (r.grad x - hRes.grad x)) := by
    calc
      _ = volumeAverage (openCubeSet Q)
          (boundaryCorrectedFluxCutoffPairingDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
            (fun x ↦ v.toFun x - hComp.toFun x) v.grad (fun _ ↦ 0)) := by
        apply volumeAverage_eq_of_ae_eq
        filter_upwards with x
        simp [hComp]
      _ = -volumeAverage (openCubeSet Q) (fun x ↦
          eta x ^ 2 * vecDot
            (boundaryCorrectedFlux
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) v.grad (fun _ ↦ 0) x)
            (v.grad x - hComp.grad x)) := hpairRaw
      _ = _ := by
        congr 1
        apply volumeAverage_eq_of_ae_eq
        filter_upwards with x
        simp [hComp, boundaryCorrectedFlux]
  let cross : Vec d → ℝ := fun x ↦
    eta x ^ 2 * vecDot
      ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x) (r.grad x)
  let datumCross : Vec d → ℝ := fun x ↦
    eta x ^ 2 * vecDot
      ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x) (hRes.grad x)
  have hetaCont : Continuous (fun x ↦ eta x ^ 2) := (heta.pow 2).continuous
  have hetaSupp : HasCompactSupport (fun x ↦ eta x ^ 2) := by
    simpa only [pow_two] using! hetaCompact.mul_left (f := eta)
  have hcross0 : IntegrableOn (fun x ↦ vecDot
      ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x) (r.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q v) r.grad_memVectorL2
  have hcross : IntegrableOn cross (openCubeSet Q) :=
    integrableOn_mul_left_of_continuous_hasCompactSupport
      hetaCont hetaSupp hcross0
  have hdatumCross0 : IntegrableOn (fun x ↦ vecDot
      ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x) (hRes.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q v) hRes.grad_memVectorL2
  have hdatumCross : IntegrableOn datumCross (openCubeSet Q) :=
    integrableOn_mul_left_of_continuous_hasCompactSupport
      hetaCont hetaSupp hdatumCross0
  have hmainR : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega r.grad_memVectorL2
        heta hetaCompact
  have hmainV : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega v.grad_memVectorL2
        heta hetaCompact
  have henergySplit : volumeAverage (openCubeSet Q)
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) =
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad) +
        volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
        2 * volumeAverage (openCubeSet Q) cross := by
    have hvec (x y : Vec d) : vecNormSq (x + y) =
        vecNormSq x + vecNormSq y + 2 * vecDot y x := by
      unfold vecNormSq vecDot
      simp only [Pi.add_apply]
      calc
        (∑ i, (x i + y i) * (x i + y i)) =
            ∑ i, ((x i * x i + y i * y i) + 2 * (y i * x i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i, (x i * x i + y i * y i)) +
              ∑ i, 2 * (y i * x i) := Finset.sum_add_distrib
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hpoint : ∀ x,
        boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad x =
          boundaryCoerciveMainDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad x +
            boundaryCoerciveMainDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad x +
            2 * cross x := by
      intro x
      unfold boundaryCoerciveMainDensity cross
      rw [hgrad x]
      rw [hvec]
      rw [vecDot_smul_left]
      ring
    have hfun :
        boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad =
          (boundaryCoerciveMainDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad +
            boundaryCoerciveMainDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
            (2 : ℝ) • cross := by
      funext x
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using! hpoint x
    rw [hfun]
    calc
      volumeAverage (openCubeSet Q)
          ((boundaryCoerciveMainDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad +
            boundaryCoerciveMainDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
            (2 : ℝ) • cross) =
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveMainDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad +
               boundaryCoerciveMainDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
            volumeAverage (openCubeSet Q) ((2 : ℝ) • cross) :=
        volumeAverage_add (hmainR.add hmainV) (by
          simpa only [Pi.smul_apply, smul_eq_mul] using! hcross.const_mul 2)
      _ = _ := by
        rw [volumeAverage_add hmainR hmainV, volumeAverage_smul]
  have hpairSplit : volumeAverage (openCubeSet Q) (fun x ↦
      eta x ^ 2 * vecDot
        ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
        (r.grad x - hRes.grad x)) =
      volumeAverage (openCubeSet Q) cross -
        volumeAverage (openCubeSet Q) datumCross := by
    have hvec (a b c : Vec d) : vecDot a (b - c) =
        vecDot a b - vecDot a c := by
      unfold vecDot
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    have hfun : (fun x ↦
        eta x ^ 2 * vecDot
          ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
          (r.grad x - hRes.grad x)) = cross - datumCross := by
      funext x
      simp only [cross, datumCross, Pi.sub_apply, hvec]
      ring
    rw [hfun, volumeAverage_sub hcross hdatumCross]
  rw [hpairSplit] at hpair
  dsimp only [cross, datumCross] at henergySplit hpair ⊢
  linarith only [henergySplit, hpair]

/-- Half-absorbable consequence of the signed affine energy split.  The only
prices are the residual energy, the canonical lift energy, and the residual
datum energy; no energy of `v - ell` occurs. -/
theorem volumeAverage_localizedAffineEnergySplit_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u r v hRes : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = r.grad x + v.grad x)
    (hweakV : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ r.toFun x - hRes.toFun x))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaSupport : tsupport eta ⊆ V) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveMainDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
      2 * volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          (fun x ↦ r.toFun x - hRes.toFun x) v.grad (fun _ ↦ 0)) ≤
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad) +
        2 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
        volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta hRes.grad) := by
  have hid := volumeAverage_localizedAffineEnergySplit_identity
    M L omega Q u r v hRes hgrad hweakV hzero heta hetaCompact hetaSupport
  let cross : Vec d → ℝ := fun x ↦
    eta x ^ 2 * vecDot
      ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x) (hRes.grad x)
  have hetaCont : Continuous (fun x ↦ eta x ^ 2) := (heta.pow 2).continuous
  have hetaSupp : HasCompactSupport (fun x ↦ eta x ^ 2) := by
    simpa only [pow_two] using! hetaCompact.mul_left (f := eta)
  have hcross0 : IntegrableOn (fun x ↦ vecDot
      ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x) (hRes.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q v) hRes.grad_memVectorL2
  have hcross : IntegrableOn cross (openCubeSet Q) :=
    integrableOn_mul_left_of_continuous_hasCompactSupport
      hetaCont hetaSupp hcross0
  have hmainV : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega v.grad_memVectorL2
        heta hetaCompact
  have hmainH : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta hRes.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega hRes.grad_memVectorL2
        heta hetaCompact
  have hcrossBound : 2 * volumeAverage (openCubeSet Q) cross ≤
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
        volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta hRes.grad) := by
    have hmono : volumeAverage (openCubeSet Q) ((2 : ℝ) • cross) ≤
        volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad +
            boundaryCoerciveMainDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta hRes.grad) := by
      apply volumeAverage_le_volumeAverage_of_le_on (measurableSet_openCubeSet Q)
      · simpa only [Pi.smul_apply, smul_eq_mul] using! hcross.const_mul 2
      · exact hmainV.add hmainH
      · intro x _
        have haeta : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * eta x ^ 2 :=
          mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
            (sq_nonneg _)
        have hdot : 2 * vecDot (v.grad x) (hRes.grad x) ≤
            vecNormSq (v.grad x) + vecNormSq (hRes.grad x) := by
          have hcoord : ∀ i : Fin d,
              2 * (v.grad x i * hRes.grad x i) ≤
                v.grad x i * v.grad x i + hRes.grad x i * hRes.grad x i := by
            intro i
            nlinarith only [sq_nonneg (v.grad x i - hRes.grad x i)]
          have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦ hcoord i
          simpa only [vecNormSq, vecDot, Finset.mul_sum,
            Finset.sum_add_distrib] using! hsum
        have := mul_le_mul_of_nonneg_left hdot haeta
        calc
          ((2 : ℝ) • cross) x =
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * eta x ^ 2) *
                (2 * vecDot (v.grad x) (hRes.grad x)) := by
            simp only [cross, Pi.smul_apply, smul_eq_mul, vecDot_smul_left]
            ring
          _ ≤ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * eta x ^ 2) *
                (vecNormSq (v.grad x) + vecNormSq (hRes.grad x)) := this
          _ = (boundaryCoerciveMainDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad +
              boundaryCoerciveMainDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta hRes.grad) x := by
            simp only [boundaryCoerciveMainDensity, Pi.add_apply]
            ring
    rw [volumeAverage_smul,
      volumeAverage_add hmainV hmainH] at hmono
    exact hmono
  dsimp only [cross] at hcrossBound
  linarith only [hid, hcrossBound]

/-- The complete localized signed affine/residual weak-energy inequality.
The two cutoff pairings are kept together; all bulk correction terms have
already collapsed to residual datum, force, and canonical-lift energies. -/
theorem volumeAverage_localizedSignedAffineResidualEnergy_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u r v hRes : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
    (hgrad : ∀ x, u.grad x = r.grad x + v.grad x)
    (hweakR : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) r g)
    (hweakV : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
    (hg : MemVectorL2 (openCubeSet Q) g)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ r.toFun x - hRes.toFun x))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaSupport : tsupport eta ⊆ V) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveMainDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
      volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          (fun x ↦ r.toFun x - hRes.toFun x) r.grad g) +
      2 * volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          (fun x ↦ r.toFun x - hRes.toFun x) v.grad (fun _ ↦ 0)) ≤
      (1 / 4 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad) +
        (7 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta hRes.grad) +
        (5 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g) +
        2 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) := by
  have hres :=
    volumeAverage_aCutoff_boundaryCoerciveMain_add_pair_le_of_localizedZeroTrace
      M L omega hweakR hg hzero heta hetaCompact hetaSupport
  have hsplit := volumeAverage_localizedAffineEnergySplit_le
    M L omega Q u r v hRes hgrad hweakV hzero heta hetaCompact hetaSupport
  have hsplit' :
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
        2 * volumeAverage (openCubeSet Q)
          (boundaryCorrectedFluxCutoffPairingDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
            (fun x ↦ r.toFun x - hRes.toFun x) v.grad (fun _ ↦ 0)) ≤
        volumeAverage (openCubeSet Q)
            (boundaryCoerciveMainDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad) +
          2 * volumeAverage (openCubeSet Q)
            (boundaryCoerciveMainDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
          volumeAverage (openCubeSet Q)
            (boundaryCoerciveDatumDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta hRes.grad) := by
    simpa only [boundaryCoerciveMainDensity, boundaryCoerciveDatumDensity]
      using! hsplit
  linarith only [hres, hsplit']

/-- Consecutive-radius signed weak-energy step.  The finite-height estimate is
used only on the residual pairing, after the physical weak equation and the
affine covariance have fixed its sign. -/
theorem boundaryCrossScale_physicalHalfAbsorbable_of_signedResidualPair
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    (u h v ell : H1Function (openCubeSet Q)) (g : Vec d → Vec d)
    (hweakU : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g)
    (hweakRes : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) (u - v) g)
    (hweakV : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hphysical : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube Q center 1)
      (fun x ↦ u.toFun x - h.toFun x))
    (haffine : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (Set.univ : Set (Vec d)) (fun x ↦ v.toFun x - ell.toFun x))
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (houter : rhoOuter < 1) {Ad Ag J P : ℝ}
    (hdatum : volumeAverage (openCubeSet Q)
      (boundaryCoerciveDatumDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
        h.grad) ≤ Ad)
    (hforce : volumeAverage (openCubeSet Q)
      (boundaryCoerciveForceDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) g) ≤ Ag)
    (hjoint : volumeAverage (openCubeSet Q) (fun x ↦
      (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x) ^ 2 *
        (((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) / 2) *
            vecNormSq (u.grad x - h.grad x) +
          2 * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (h.grad x - ell.grad x) +
          2 * (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ *
            vecNormSq (g x) +
          (3 * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x / 2) *
            vecNormSq (v.grad x))) ≤ J)
    (hpair : |volumeAverage (openCubeSet Q)
      (boundaryCorrectedFluxCutoffPairingDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
        (fun x ↦ (u - v).toFun x - (h - ell).toFun x)
        (u - v).grad g)| ≤
      (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
        (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (u.grad x)) + P) :
    boundaryCrossScaleEnergyProfile Q Q center rhoInner
        (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (u.grad x)) +
        (5 / 2 : ℝ) * Ad + (5 / 2 : ℝ) * Ag + J + P := by
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta :=
    coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter
  have hetaCompact : HasCompactSupport eta :=
    coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner hinnerOuter
  have hetaSupport : tsupport eta ⊆
      coarseCaccioppoliLocalOpenCube Q center 1 :=
    (coarseCaccioppoliLocalCanonicalFun_tsupport_subset_localClosedCube
      hinner hinnerOuter).trans
      (coarseCaccioppoliLocalClosedCube_subset_localOpenCube_one_of_lt_one houter)
  have hsigned := volumeAverage_physicalMain_add_residualPair_le_jointBudget
    M L omega Q u h v ell g hweakU hweakRes hweakV hg hphysical haffine
      heta hetaCompact hetaSupport
  have henergy := integrableOn_aCutoff_energy M L omega Q u
  have hmain : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega u.grad_memVectorL2
        heta hetaCompact
  have hinnerMain := boundaryCrossScaleEnergyProfile_le_boundaryCoerciveMain
    hinner hinnerOuter
    (fun x _ => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
    henergy hmain
  have hmainOuter :=
    volumeAverage_boundaryCoerciveMain_localCanonicalFun_le_outerProfile
      hinner hinnerOuter
      (fun x _ => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
      henergy hmain
  have hpairNeg :
      -volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          (fun x ↦ (u - v).toFun x - (h - ell).toFun x)
          (u - v).grad g) ≤
        |volumeAverage (openCubeSet Q)
          (boundaryCorrectedFluxCutoffPairingDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
            (fun x ↦ (u - v).toFun x - (h - ell).toFun x)
            (u - v).grad g)| := neg_le_abs _
  dsimp only [eta] at hsigned hinnerMain hmainOuter hpairNeg hpair hdatum hforce hjoint ⊢
  linarith only [hsigned, hinnerMain, hmainOuter, hpairNeg, hpair,
    hdatum, hforce, hjoint]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
