module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCanonicalGradient
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryLocalizedCoerciveTest
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.EnergyHalf

@[expose] public section

/-!
# Integrability of the direct boundary cutoff test

The scalar cutoff coefficient is continuous and uniformly elliptic on every
parent cube.  Consequently all densities in the direct squared-cutoff weak
test are integrable.  This removes the bookkeeping hypotheses from the
radius-iteration input.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory
open Homogenization.WeakPoissonEquationOn

noncomputable section

variable {d : ℕ}



theorem memVectorL2_aCutoff_smul_grad
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q)
      (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x • u.grad x) := by
  have hflux := memVectorL2_flux Q (aCutoffFamily M L omega) u
  apply hflux.ae_eq
  filter_upwards with x
  simp only [aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
    Homogenization.matVecMul_scalarMatrix]

theorem integrableOn_aCutoff_energy
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    IntegrableOn (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
      vecNormSq (u.grad x)) (openCubeSet Q) := by
  have hpair := integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2
    (memVectorL2_aCutoff_smul_grad M L omega Q u)
  apply hpair.congr_fun
  · intro x _
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · exact measurableSet_openCubeSet Q

theorem integrableOn_aCutoff_sqCutoff_vecNormSq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet Q) G)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    IntegrableOn (fun x =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * eta x ^ 2 * vecNormSq (G x))
      (openCubeSet Q) := by
  have hGsq : IntegrableOn (fun x => vecNormSq (G x)) (openCubeSet Q) := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hG hG
  have hphiCont : Continuous (fun x =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * eta x ^ 2) :=
    (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).mul
      (heta.pow 2).continuous
  have hetaSqCompact : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using! hetaCompact.mul_left (f := eta)
  have hphiCompact : HasCompactSupport (fun x =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * eta x ^ 2) :=
    hetaSqCompact.mul_left
  exact integrableOn_mul_left_of_continuous_hasCompactSupport
    hphiCont hphiCompact hGsq

private theorem integrableOn_aCutoff_cutoffDensity
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} {w : Vec d → ℝ} (hw : MemScalarL2 (openCubeSet Q) w)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    IntegrableOn (boundaryCoerciveCutoffDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w) (openCubeSet Q) := by
  have hwsq : IntegrableOn (fun x => w x ^ 2) (openCubeSet Q) := by
    simpa [pow_two, IntegrableOn, volumeMeasureOn, Pi.mul_def] using! hw.integrable_mul hw
  have hphiCont : Continuous (fun x =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
        vecNormSq (euclideanGradient eta x)) :=
    (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).mul
      (continuous_vecNormSq_euclideanGradient_of_contDiff heta)
  have hphiCompact : HasCompactSupport (fun x =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
        vecNormSq (euclideanGradient eta x)) :=
    (hasCompactSupport_vecNormSq_euclideanGradient hetaCompact).mul_left
  have hmul := integrableOn_mul_left_of_continuous_hasCompactSupport
    hphiCont hphiCompact hwsq
  apply hmul.congr_fun
  · intro x _
    simp only [boundaryCoerciveCutoffDensity]
    ring
  · exact measurableSet_openCubeSet Q

private theorem integrableOn_aCutoff_forceDensity
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet Q) G)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    IntegrableOn (boundaryCoerciveForceDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta G) (openCubeSet Q) := by
  have hGsq : IntegrableOn (fun x => vecNormSq (G x)) (openCubeSet Q) := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hG hG
  have haInvCont : Continuous (fun x =>
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) :=
    (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).inv₀
      (fun x => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).ne')
  have hphiCont : Continuous (fun x =>
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ * eta x ^ 2) :=
    haInvCont.mul (heta.pow 2).continuous
  have hetaSqCompact : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using! hetaCompact.mul_left (f := eta)
  have hphiCompact : HasCompactSupport (fun x =>
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ * eta x ^ 2) :=
    hetaSqCompact.mul_left
  exact integrableOn_mul_left_of_continuous_hasCompactSupport
    hphiCont hphiCompact hGsq



theorem integrableOn_aCutoff_boundaryCoerciveCutoffDensity
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} {w : Vec d → ℝ} (hw : MemScalarL2 (openCubeSet Q) w)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    IntegrableOn (boundaryCoerciveCutoffDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w) (openCubeSet Q) :=
  integrableOn_aCutoff_cutoffDensity M L omega hw heta hetaCompact



theorem integrableOn_aCutoff_boundaryCoerciveForceDensity
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet Q) G)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    IntegrableOn (boundaryCoerciveForceDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta G) (openCubeSet Q) :=
  integrableOn_aCutoff_forceDensity M L omega hG heta hetaCompact

/-- Localized-trace form of the direct GMC cutoff estimate.  This is the
analytic carrier used by a projected boundary cell: the cutoff is supported
in the physical-boundary window, while artificial faces of the projected
cube impose no trace condition. -/
theorem setIntegral_aCutoff_boundaryCoerciveMain_le_of_localizedZeroTrace
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
    ∫ x in openCubeSet Q,
        boundaryCoerciveMainDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad x ∂volume ≤
      4 * ∫ x in openCubeSet Q,
          boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta h.grad x ∂volume +
        14 * ∫ x in openCubeSet Q,
          boundaryCoerciveCutoffDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
            (fun y => u.toFun y - h.toFun y) x ∂volume +
        8 * ∫ x in openCubeSet Q,
          boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g x ∂volume := by
  let w : Vec d → ℝ := fun y => u.toFun y - h.toFun y
  have hw : MemScalarL2 (openCubeSet Q) w := by
    simpa [w, MemScalarL2, volumeMeasureOn, Pi.sub_def] using! u.memL2.sub h.memL2
  have htest : MemVectorL2 (openCubeSet Q)
      (boundarySqCutoffTestGradient eta u h) := by
    let etaSq : Vec d → ℝ := fun x => eta x ^ 2
    have hetaSq : ContDiff ℝ (⊤ : ℕ∞) etaSq := heta.pow 2
    have hetaSqCompact : HasCompactSupport etaSq := by
      dsimp only [etaSq]
      simpa only [pow_two, Pi.mul_def] using! hetaCompact.mul_left (f := eta)
    let wH : H1Function (openCubeSet Q) := u - h
    let psi := wH.mulContDiffHasCompactSupport hetaSq hetaSqCompact
    have hpsiGrad : psi.grad = boundarySqCutoffTestGradient eta u h := by
      funext x i
      rw [show psi = wH.mulContDiffHasCompactSupport hetaSq hetaSqCompact by rfl,
        H1Function.mulContDiffHasCompactSupport_grad]
      change eta x ^ 2 * wH.grad x i + wH.toFun x *
          (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) = _
      rw [show (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) =
          2 * eta x * euclideanGradient eta x i by
        simpa [euclideanCoordDeriv] using! euclideanCoordDeriv_sq heta i x]
      simp only [wH, H1Function.sub_grad, H1Function.sub_toFun]
      rfl
    simpa only [hpsiGrad] using psi.grad_memVectorL2
  have hmain : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad)
      (openCubeSet Q) := by
    unfold boundaryCoerciveMainDensity
    simpa only using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega u.grad_memVectorL2
        heta hetaCompact
  have hdatum : IntegrableOn
      (boundaryCoerciveDatumDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta h.grad)
      (openCubeSet Q) := by
    unfold boundaryCoerciveDatumDensity
    simpa only using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega h.grad_memVectorL2
        heta hetaCompact
  have hcutoff := integrableOn_aCutoff_cutoffDensity M L omega hw heta hetaCompact
  have hforce := integrableOn_aCutoff_forceDensity M L omega hg heta hetaCompact
  have hweakLeft : IntegrableOn
      (boundaryCoerciveWeakLeftDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w u.grad h.grad)
      (openCubeSet Q) := by
    have hpair := integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q u) htest
    simpa only [boundaryCoerciveWeakLeftDensity,
      boundarySqCutoffTestGradient, w] using! hpair
  have hweakForce : IntegrableOn
      (boundaryCoerciveWeakForceDensity eta w u.grad h.grad g)
      (openCubeSet Q) := by
    have hpair := integrableOn_vecDot_of_memVectorL2 hg htest
    simpa only [boundaryCoerciveWeakForceDensity,
      boundarySqCutoffTestGradient, w] using! hpair
  have hrhs : IntegrableOn
      (boundaryCoerciveRhsDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w u.grad h.grad g)
      (openCubeSet Q) := by
    have hsum : IntegrableOn (fun x =>
        boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad x -
          boundaryCoerciveWeakLeftDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w u.grad h.grad x -
          boundaryCoerciveWeakForceDensity eta w u.grad h.grad g x)
        (openCubeSet Q) := (hmain.sub hweakLeft).sub hweakForce
    apply hsum.congr_fun
    · intro x _
      dsimp only
      have hleft := boundaryCoercive_main_sub_weakLeft
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w u.grad h.grad x
      have hright := boundaryCoercive_rhs_add_weakForce
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w u.grad h.grad g x
      linarith only [hleft, hright]
    · exact measurableSet_openCubeSet Q
  have hweakIdentity :=
    setIntegral_boundarySqCutoffTestGradient_identity_of_localizedZeroTrace
      hweak hzero heta hetaCompact hetaSupport
  apply setIntegral_boundaryCoerciveMain_le_of_weak_identity
    (fun x _ => SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x)
    hmain hweakLeft hweakForce hrhs hdatum hcutoff hforce
  simpa only [boundaryCoerciveWeakLeftDensity,
    boundaryCoerciveWeakForceDensity, boundarySqCutoffTestGradient, w] using!
      hweakIdentity

/-- The canonical direct boundary estimate for the GMC cutoff, with every
measure-theoretic side condition discharged. -/
theorem coarseCaccioppoliLocalEnergyProfile_le_aCutoff_boundaryCoerciveTerms
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hdir : IsDirichletSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) Q u h g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter) :
    coarseCaccioppoliLocalEnergyProfile Q center rhoInner
        (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      4 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) h.grad) +
        14 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveCutoffDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
            (fun y => u.toFun y - h.toFun y)) +
        8 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) g) := by
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter
  let w : Vec d → ℝ := fun y => u.toFun y - h.toFun y
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta :=
    coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter
  have hetaCompact : HasCompactSupport eta :=
    coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner hinnerOuter
  have hw : MemScalarL2 (openCubeSet Q) w := by
    simpa [w, MemScalarL2, volumeMeasureOn, Pi.sub_def] using! u.memL2.sub h.memL2
  have htest : MemVectorL2 (openCubeSet Q)
      (boundarySqCutoffTestGradient eta u h) :=
    memVectorL2_boundarySqCutoffTestGradient hdir.1 heta hetaCompact
  have hmain : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad)
      (openCubeSet Q) := by
    unfold boundaryCoerciveMainDensity
    simpa only using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega u.grad_memVectorL2
        heta hetaCompact
  have hdatum : IntegrableOn
      (boundaryCoerciveDatumDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta h.grad)
      (openCubeSet Q) := by
    unfold boundaryCoerciveDatumDensity
    simpa only using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega h.grad_memVectorL2
        heta hetaCompact
  have hcutoff := integrableOn_aCutoff_cutoffDensity M L omega hw heta hetaCompact
  have hforce := integrableOn_aCutoff_forceDensity M L omega hg heta hetaCompact
  have hweakLeft : IntegrableOn
      (boundaryCoerciveWeakLeftDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w u.grad h.grad)
      (openCubeSet Q) := by
    have hpair := integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q u) htest
    simpa only [boundaryCoerciveWeakLeftDensity,
      boundarySqCutoffTestGradient, w] using! hpair
  have hweakForce : IntegrableOn
      (boundaryCoerciveWeakForceDensity eta w u.grad h.grad g)
      (openCubeSet Q) := by
    have hpair := integrableOn_vecDot_of_memVectorL2 hg htest
    simpa only [boundaryCoerciveWeakForceDensity,
      boundarySqCutoffTestGradient, w] using! hpair
  have hrhs : IntegrableOn
      (boundaryCoerciveRhsDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w u.grad h.grad g)
      (openCubeSet Q) := by
    have hsum : IntegrableOn (fun x =>
        boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad x -
          boundaryCoerciveWeakLeftDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w u.grad h.grad x -
          boundaryCoerciveWeakForceDensity eta w u.grad h.grad g x)
        (openCubeSet Q) :=
      (hmain.sub hweakLeft).sub hweakForce
    apply hsum.congr_fun
    · intro x _
      dsimp only
      have hleft := boundaryCoercive_main_sub_weakLeft
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w u.grad h.grad x
      have hright := boundaryCoercive_rhs_add_weakForce
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta w u.grad h.grad g x
      linarith only [hleft, hright]
    · exact measurableSet_openCubeSet Q
  have henergyOpen := integrableOn_aCutoff_energy M L omega Q u
  have henergyCube : IntegrableOn (fun x =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x))
      (cubeSet Q) := by
    simpa only [IntegrableOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using henergyOpen
  exact coarseCaccioppoliLocalEnergyProfile_le_boundaryCoerciveTerms
    hdir hinner hinnerOuter
    (fun x _ => SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x)
    (fun x _ => SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x)
    henergyCube hmain hweakLeft hweakForce hrhs hdatum hcutoff hforce

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
