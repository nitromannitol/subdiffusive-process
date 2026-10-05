module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAffineResidual
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryLocalizedCoerciveTest

@[expose] public section

/-!
# Affine covariance of the active-cell cutoff pairing

The affine boundary mode is removed before the finite-height product norm is
formed.  The corrected flux is affine in the solution gradient, so subtracting
the canonical zero-force lift produces one explicit coefficient-flux pairing.
That pairing is tested against the zero-trace correction `v - ell`; it is
therefore an energy term, not a low-frequency term carrying the annular gap.

This is the active-cell affine split preceding the boundary remainder. The extra
corrected-flux identity is specific to the GMC scalar coefficient.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
  Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Subtracting a gradient from the solution flux leaves one explicit scalar
coefficient-flux term.  This identity is applied before any Besov or `L²`
norm is taken. -/
theorem boundaryCorrectedFluxCutoffPairingDensity_sub_grad
    (a eta w : Vec d → ℝ) (U V G : Vec d → Vec d) (x : Vec d) :
    boundaryCorrectedFluxCutoffPairingDensity a eta w
        (fun y ↦ U y - V y) G x =
      boundaryCorrectedFluxCutoffPairingDensity a eta w U G x -
        vecDot ((a x) • V x)
          (w x • scalarCutoffGradientField (fun y ↦ eta y ^ 2) x) := by
  simp only [boundaryCorrectedFluxCutoffPairingDensity, boundaryCorrectedFlux,
    vecDot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The zero-trace correction is split from the scalar cutoff factor before
the finite-height low-frequency estimate. -/
theorem boundaryCorrectedFluxCutoffPairingDensity_sub_value
    (a eta w r : Vec d → ℝ) (U G : Vec d → Vec d) (x : Vec d) :
    boundaryCorrectedFluxCutoffPairingDensity a eta (fun y ↦ w y - r y) U G x =
      boundaryCorrectedFluxCutoffPairingDensity a eta w U G x -
        boundaryCorrectedFluxCutoffPairingDensity a eta r U G x := by
  simp only [boundaryCorrectedFluxCutoffPairingDensity, vecDot,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Full affine covariance of the residual cutoff pairing.  The first term is
the physical low-frequency pairing; the other three terms contain the
canonical affine correction and are handled by its weak equation and energy.
-/
theorem boundaryCorrectedFluxCutoffPairingDensity_affineResidual
    (a eta w r : Vec d → ℝ) (U V G : Vec d → Vec d) (x : Vec d) :
    boundaryCorrectedFluxCutoffPairingDensity a eta (fun y ↦ w y - r y)
        (fun y ↦ U y - V y) G x =
      boundaryCorrectedFluxCutoffPairingDensity a eta w U G x -
        boundaryCorrectedFluxCutoffPairingDensity a eta r U G x -
        vecDot ((a x) • V x)
          (w x • scalarCutoffGradientField (fun y ↦ eta y ^ 2) x) +
        vecDot ((a x) • V x)
          (r x • scalarCutoffGradientField (fun y ↦ eta y ^ 2) x) := by
  simp only [boundaryCorrectedFluxCutoffPairingDensity, boundaryCorrectedFlux,
    vecDot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Bilinear form of the affine split.  The only positive-Besov product to
which the descendant estimate is applied is the first term, built from the
residual value and residual flux.  The two remaining pairings are global
weak-test terms and are priced before the finite-height norm is formed. -/
theorem boundaryCorrectedFluxCutoffPairingDensity_affineBilinear
    (a eta w r : Vec d → ℝ) (U V G : Vec d → Vec d) (x : Vec d) :
    boundaryCorrectedFluxCutoffPairingDensity a eta w U G x =
      boundaryCorrectedFluxCutoffPairingDensity a eta (fun y ↦ w y - r y)
          (fun y ↦ U y - V y) G x +
        boundaryCorrectedFluxCutoffPairingDensity a eta r
          (fun y ↦ U y - V y) G x +
        boundaryCorrectedFluxCutoffPairingDensity a eta w V (fun _ ↦ 0) x := by
  simp only [boundaryCorrectedFluxCutoffPairingDensity, boundaryCorrectedFlux,
    vecDot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.zero_apply]
  ring

/-- Scalar Young price for the bulk term left by the affine correction's weak
equation.  The cutoff is bounded by one, so no derivative or annular gap
appears. -/
theorem abs_affineCorrectionBulk_le_energy
    {a eta : ℝ} {V p : Vec d} (ha : 0 ≤ a) (heta : |eta| ≤ 1) :
    |a * eta ^ 2 * vecDot V (V - p)| ≤
      (3 / 2 : ℝ) * (a * vecNormSq V) +
        (1 / 2 : ℝ) * (a * vecNormSq p) := by
  have hetaSq : eta ^ 2 ≤ 1 := by
    have hs := (sq_le_sq₀ (abs_nonneg eta) (by norm_num)).2 heta
    simpa [sq_abs] using hs
  have hdotEq : vecDot V (V - p) = vecNormSq V - vecDot V p := by
    simp only [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, vecNormSq]
  have hdot : |vecDot V (V - p)| ≤
      (3 / 2 : ℝ) * vecNormSq V + (1 / 2 : ℝ) * vecNormSq p := by
    rw [hdotEq]
    calc
      |vecNormSq V - vecDot V p| ≤
          |vecNormSq V| + |vecDot V p| := abs_sub _ _
      _ ≤ vecNormSq V +
          (vecNormSq V / 2 + vecNormSq p / 2) := by
        rw [abs_of_nonneg (vecNormSq_nonneg V)]
        gcongr
        exact abs_vecDot_le_add_halves_vecNormSq V p
      _ = (3 / 2 : ℝ) * vecNormSq V +
          (1 / 2 : ℝ) * vecNormSq p := by ring
  have heta0 : 0 ≤ eta ^ 2 := sq_nonneg eta
  have hbudget0 : 0 ≤ (3 / 2 : ℝ) * vecNormSq V +
      (1 / 2 : ℝ) * vecNormSq p :=
    add_nonneg
      (mul_nonneg (by norm_num) (vecNormSq_nonneg V))
      (mul_nonneg (by norm_num) (vecNormSq_nonneg p))
  have hscale : a * eta ^ 2 * |vecDot V (V - p)| ≤
      a * ((3 / 2 : ℝ) * vecNormSq V +
        (1 / 2 : ℝ) * vecNormSq p) := by
    calc
      a * eta ^ 2 * |vecDot V (V - p)| ≤
          a * eta ^ 2 * ((3 / 2 : ℝ) * vecNormSq V +
            (1 / 2 : ℝ) * vecNormSq p) := by
        gcongr
      _ ≤ a * 1 * ((3 / 2 : ℝ) * vecNormSq V +
            (1 / 2 : ℝ) * vecNormSq p) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hetaSq ha) hbudget0
      _ = a * ((3 / 2 : ℝ) * vecNormSq V +
            (1 / 2 : ℝ) * vecNormSq p) := by ring
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg heta0]
  calc
    a * eta ^ 2 * |vecDot V (V - p)| ≤
        a * ((3 / 2 : ℝ) * vecNormSq V +
          (1 / 2 : ℝ) * vecNormSq p) := hscale
    _ = (3 / 2 : ℝ) * (a * vecNormSq V) +
        (1 / 2 : ℝ) * (a * vecNormSq p) := by ring

/-- Averaged form of `abs_affineCorrectionBulk_le_energy`.  This is the
dimensionless estimate which keeps the affine correction outside the
active-cell low-frequency budget. -/
theorem abs_volumeAverage_affineCorrectionBulk_le_energy
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (v ell : H1Function (openCubeSet Q)) (p : Vec d)
    (hell : ∀ x, ell.grad x = p)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta)
    (hetaOne : ∀ x ∈ openCubeSet Q, |eta x| ≤ 1) :
    |volumeAverage (openCubeSet Q) (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * eta x ^ 2 *
          vecDot (v.grad x) (v.grad x - p))| ≤
      volumeAverage (openCubeSet Q) (fun x ↦
        (3 / 2 : ℝ) *
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)) +
          (1 / 2 : ℝ) *
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq p)) := by
  let bulk : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * eta x ^ 2 *
      vecDot (v.grad x) (v.grad x - p)
  let R : Vec d → ℝ := fun x ↦
    (3 / 2 : ℝ) *
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)) +
      (1 / 2 : ℝ) *
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq p)
  have hvInt : IntegrableOn (fun x ↦
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x))
      (openCubeSet Q) := integrableOn_aCutoff_energy M L omega Q v
  have hpInt : IntegrableOn (fun x ↦
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq p)
      (openCubeSet Q) := by
    have h := integrableOn_aCutoff_energy M L omega Q ell
    apply h.congr_fun
    · intro x _
      change _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (ell.grad x) = _
      rw [hell x]
    · exact measurableSet_openCubeSet Q
  have hRInt : IntegrableOn R (openCubeSet Q) := by
    dsimp only [R]
    exact (hvInt.const_mul (3 / 2 : ℝ)).add
      (hpInt.const_mul (1 / 2 : ℝ))
  have hpairInt : IntegrableOn
      (boundaryCorrectedFluxCutoffPairingDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
        (fun x ↦ v.toFun x - ell.toFun x) v.grad (fun _ ↦ 0))
      (openCubeSet Q) := by
    have hzeroL2 : MemVectorL2 (openCubeSet Q) (fun _ : Vec d ↦ (0 : Vec d)) := by
      simp [MemVectorL2, volumeMeasureOn]
    exact integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
      M L omega v ell hzeroL2 heta hetaCompact
  have htest : MemVectorL2 (openCubeSet Q)
      (boundarySqCutoffTestGradient eta v ell) :=
    memVectorL2_boundarySqCutoffTestGradient_of_smooth_compact
      v ell heta hetaCompact
  have htotal : IntegrableOn (fun x ↦
      vecDot ((_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) • v.grad x)
        (boundarySqCutoffTestGradient eta v ell x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q v) htest
  have hbulkInt : IntegrableOn bulk (openCubeSet Q) := by
    have hsub := htotal.sub hpairInt
    apply hsub.congr
    filter_upwards with x
    have hsqGrad : scalarCutoffGradientField (fun y ↦ eta y ^ 2) x =
        (2 * eta x) • euclideanGradient eta x := by
      funext i
      change euclideanCoordDeriv i (fun y ↦ eta y ^ 2) x =
        (2 * eta x) * euclideanCoordDeriv i eta x
      exact euclideanCoordDeriv_sq heta i x
    have htestGrad : boundarySqCutoffTestGradient eta v ell x =
        (eta x ^ 2) • (v.grad x - p) +
          (v.toFun x - ell.toFun x) •
            scalarCutoffGradientField (fun y ↦ eta y ^ 2) x := by
      funext i
      simp only [boundarySqCutoffTestGradient, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, hell x, hsqGrad]
    change vecDot ((_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) • v.grad x)
          (boundarySqCutoffTestGradient eta v ell x) -
        boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
          (fun x ↦ v.toFun x - ell.toFun x) v.grad (fun _ ↦ 0) x = bulk x
    rw [htestGrad, vecDot_add_right, vecDot_smul_right, vecDot_smul_left]
    dsimp only [bulk, boundaryCorrectedFluxCutoffPairingDensity,
      boundaryCorrectedFlux]
    simp only [add_zero]
    rw [vecDot_smul_left]
    ring
  have hpoint : ∀ x ∈ openCubeSet Q, |bulk x| ≤ R x := by
    intro x hx
    exact abs_affineCorrectionBulk_le_energy
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le (hetaOne x hx)
  have habsIntegral : |∫ x in openCubeSet Q, bulk x ∂volume| ≤
      ∫ x in openCubeSet Q, |bulk x| ∂volume :=
    abs_integral_le_integral_abs
  have hmono : (∫ x in openCubeSet Q, |bulk x| ∂volume) ≤
      ∫ x in openCubeSet Q, R x ∂volume := by
    exact setIntegral_mono_on hbulkInt.abs hRInt
      (measurableSet_openCubeSet Q) hpoint
  unfold volumeAverage
  dsimp only [bulk, R]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (ENNReal.toReal_nonneg))]
  exact mul_le_mul_of_nonneg_left (habsIntegral.trans hmono)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)



theorem volumeAverage_aCutoff_vecNormSq_eq_localizedCoeffEnergyValue
    [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) =
      localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) u := by
  rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
    (Set.Subset.rfl) u]
  apply volumeAverage_eq_of_ae_eq
  filter_upwards
      [publicCoeffField_ae_eq_openCubeSet Q (aCutoffFamily M L omega)] with x hx
  simp only [coefficientEnergyDensity, hx]
  simp [aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
    Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
    vecDot_smul_right, vecNormSq]

/-- A localized weak solution converts its complete corrected-flux cutoff
pairing into a bulk gradient pairing.  This is the affine-covariant seam:
after the value/flux split, the correction terms are tested globally rather
than inserted into the finite-height positive-Besov norm. -/
theorem volumeAverage_boundaryCorrectedFluxCutoffPairing_eq_neg_bulk
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u h : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ u.toFun x - h.toFun x))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaSupport : tsupport eta ⊆ V) :
    volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
          (fun x ↦ u.toFun x - h.toFun x) u.grad g) =
      -volumeAverage (openCubeSet Q) (fun x ↦
        eta x ^ 2 *
          vecDot
            (boundaryCorrectedFlux
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) u.grad g x)
            (u.grad x - h.grad x)) := by
  let a := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  let pair : Vec d → ℝ :=
    boundaryCorrectedFluxCutoffPairingDensity a eta
      (fun x ↦ u.toFun x - h.toFun x) u.grad g
  let bulk : Vec d → ℝ := fun x ↦
    eta x ^ 2 * vecDot (boundaryCorrectedFlux a u.grad g x)
      (u.grad x - h.grad x)
  have hpoint : ∀ x,
      vecDot (boundaryCorrectedFlux a u.grad g x)
          (boundarySqCutoffTestGradient eta u h x) = bulk x + pair x := by
    intro x
    have hsqGrad : scalarCutoffGradientField (fun y ↦ eta y ^ 2) x =
        (2 * eta x) • euclideanGradient eta x := by
      funext i
      change euclideanCoordDeriv i (fun y ↦ eta y ^ 2) x =
          (2 * eta x) * euclideanCoordDeriv i eta x
      exact euclideanCoordDeriv_sq heta i x
    have htestGrad : boundarySqCutoffTestGradient eta u h x =
        (eta x ^ 2) • (u.grad x - h.grad x) +
          (u.toFun x - h.toFun x) •
            scalarCutoffGradientField (fun y ↦ eta y ^ 2) x := by
      funext i
      simp only [boundarySqCutoffTestGradient, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, hsqGrad]
    rw [htestGrad, vecDot_add_right, vecDot_smul_right]
    rfl
  have hpairInt : IntegrableOn pair (openCubeSet Q) := by
    dsimp only [pair, a]
    exact integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
      M L omega u h hg heta hetaCompact
  have htest : MemVectorL2 (openCubeSet Q)
      (boundarySqCutoffTestGradient eta u h) :=
    memVectorL2_boundarySqCutoffTestGradient_of_smooth_compact
      u h heta hetaCompact
  have hflux : MemVectorL2 (openCubeSet Q)
      (boundaryCorrectedFlux a u.grad g) := by
    exact (memVectorL2_aCutoff_smul_grad M L omega Q u).add hg
  have htotal : IntegrableOn (fun x ↦
      vecDot (boundaryCorrectedFlux a u.grad g x)
        (boundarySqCutoffTestGradient eta u h x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hflux htest
  have hbulkInt : IntegrableOn bulk (openCubeSet Q) := by
    have hsub := htotal.sub hpairInt
    apply hsub.congr
    filter_upwards with x
    change vecDot (boundaryCorrectedFlux a u.grad g x)
        (boundarySqCutoffTestGradient eta u h x) - pair x = bulk x
    rw [hpoint x]
    ring
  have hid :=
    setIntegral_boundarySqCutoffTestGradient_identity_of_localizedZeroTrace
      hweak hzero heta hetaCompact hetaSupport
  have haTestInt : IntegrableOn (fun x ↦
      vecDot (a x • u.grad x) (boundarySqCutoffTestGradient eta u h x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q u) htest
  have hgTestInt : IntegrableOn (fun x ↦
      vecDot (g x) (boundarySqCutoffTestGradient eta u h x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hg htest
  have hid0 : ∫ x in openCubeSet Q,
      vecDot (boundaryCorrectedFlux a u.grad g x)
        (boundarySqCutoffTestGradient eta u h x) ∂volume = 0 := by
    calc
      ∫ x in openCubeSet Q,
          vecDot (boundaryCorrectedFlux a u.grad g x)
            (boundarySqCutoffTestGradient eta u h x) ∂volume =
          ∫ x in openCubeSet Q,
            (vecDot (a x • u.grad x) (boundarySqCutoffTestGradient eta u h x) +
              vecDot (g x) (boundarySqCutoffTestGradient eta u h x)) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [boundaryCorrectedFlux, vecDot_add_left]
      _ = (∫ x in openCubeSet Q,
            vecDot (a x • u.grad x) (boundarySqCutoffTestGradient eta u h x)
              ∂volume) +
          ∫ x in openCubeSet Q,
            vecDot (g x) (boundarySqCutoffTestGradient eta u h x) ∂volume :=
        integral_add haTestInt hgTestInt
      _ = 0 := by
        have hid' : ∫ x in openCubeSet Q,
            vecDot (a x • u.grad x) (boundarySqCutoffTestGradient eta u h x)
              ∂volume =
            -∫ x in openCubeSet Q,
              vecDot (g x) (boundarySqCutoffTestGradient eta u h x) ∂volume := by
          simpa only [a] using hid
        rw [hid']
        ring
  have hsum : (∫ x in openCubeSet Q, bulk x ∂volume) +
      ∫ x in openCubeSet Q, pair x ∂volume = 0 := by
    rw [← integral_add hbulkInt hpairInt]
    calc
      ∫ x in openCubeSet Q, bulk x + pair x ∂volume =
          ∫ x in openCubeSet Q,
            vecDot (boundaryCorrectedFlux a u.grad g x)
              (boundarySqCutoffTestGradient eta u h x) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        exact (hpoint x).symm
      _ = 0 := hid0
  unfold volumeAverage
  dsimp only [pair, bulk, a]
  rw [show ∫ x in openCubeSet Q,
      boundaryCorrectedFluxCutoffPairingDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
        (fun x ↦ u.toFun x - h.toFun x) u.grad g x ∂volume =
      -∫ x in openCubeSet Q,
        eta x ^ 2 * vecDot
          (boundaryCorrectedFlux
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) u.grad g x)
          (u.grad x - h.grad x) ∂volume by linarith only [hsum]]
  ring

/-- Parent-average affine covariance for the active cutoff pairing.  The
first term is the sole term passed to the finite-height descendant estimate.
The two displayed bulk terms are the global weak tests generated by the
zero-trace affine correction and by the physical boundary difference. -/
theorem volumeAverage_boundaryCorrectedFluxCutoffPairing_affineCovariant
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u h v ell : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
    (hweakRes : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) (u - v) g)
    (hweakV : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
    (hg : MemVectorL2 (openCubeSet Q) g)
    {V : Set (Vec d)}
    (hphysical : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ u.toFun x - h.toFun x))
    (haffine : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (Set.univ : Set (Vec d)) (fun x ↦ v.toFun x - ell.toFun x))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaSupport : tsupport eta ⊆ V) :
    volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
          (fun x ↦ u.toFun x - h.toFun x) u.grad g) =
      volumeAverage (openCubeSet Q)
          (boundaryCorrectedFluxCutoffPairingDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
            (fun x ↦ (u - v).toFun x - (h - ell).toFun x)
            (u - v).grad g) -
        volumeAverage (openCubeSet Q) (fun x ↦
          eta x ^ 2 *
            vecDot
              (boundaryCorrectedFlux
                (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (u - v).grad g x)
              (v.grad x - ell.grad x)) -
        volumeAverage (openCubeSet Q) (fun x ↦
          eta x ^ 2 * vecDot
            ((_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) • v.grad x)
            (u.grad x - h.grad x)) := by
  let uRes : H1Function (openCubeSet Q) := u - v
  let hRes : H1Function (openCubeSet Q) := h - ell
  let r : H1Function (openCubeSet Q) := v - ell
  let hA : H1Function (openCubeSet Q) := uRes - r
  let w : H1Function (openCubeSet Q) := u - h
  let hB : H1Function (openCubeSet Q) := v - w
  let a := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  let physicalPair : Vec d → ℝ :=
    boundaryCorrectedFluxCutoffPairingDensity a eta w.toFun u.grad g
  let residualPair : Vec d → ℝ :=
    boundaryCorrectedFluxCutoffPairingDensity a eta
      (fun x ↦ uRes.toFun x - hRes.toFun x) uRes.grad g
  let correctionA : Vec d → ℝ :=
    boundaryCorrectedFluxCutoffPairingDensity a eta r.toFun uRes.grad g
  let correctionB : Vec d → ℝ :=
    boundaryCorrectedFluxCutoffPairingDensity a eta w.toFun v.grad (fun _ ↦ 0)
  have hzeroA : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (Set.univ : Set (Vec d)) (fun x ↦ uRes.toFun x - hA.toFun x) := by
    exact Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun x ↦ by simp [uRes, r, hA]) haffine
  have hzeroB : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ v.toFun x - hB.toFun x) := by
    exact Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun x ↦ by simp [w, hB]) hphysical
  have hzeroL2 : MemVectorL2 (openCubeSet Q) (fun _ : Vec d ↦ (0 : Vec d)) := by
    simp [MemVectorL2, volumeMeasureOn]
  have hphysicalInt : IntegrableOn physicalPair (openCubeSet Q) := by
    simpa [physicalPair, a, w, H1Function.sub_toFun] using
      integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
        M L omega u h hg heta hetaCompact
  have hresidualInt : IntegrableOn residualPair (openCubeSet Q) := by
    dsimp only [residualPair, a]
    exact integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
      M L omega uRes hRes hg heta hetaCompact
  have hcorrectionAInt : IntegrableOn correctionA (openCubeSet Q) := by
    have h := integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
      M L omega uRes hA hg heta hetaCompact
    apply h.congr_fun
    · intro x _
      simp [correctionA, a, r, hA, H1Function.sub_toFun]
    · exact measurableSet_openCubeSet Q
  have hcorrectionBInt : IntegrableOn correctionB (openCubeSet Q) := by
    have h := integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
      M L omega v hB hzeroL2 heta hetaCompact
    apply h.congr_fun
    · intro x _
      simp [correctionB, a, w, hB, H1Function.sub_toFun]
    · exact measurableSet_openCubeSet Q
  have hpoint : ∀ x,
      physicalPair x = residualPair x + correctionA x + correctionB x := by
    intro x
    simp only [physicalPair, residualPair, correctionA, correctionB, a, uRes,
      hRes, r, w, H1Function.sub_toFun, H1Function.sub_grad]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      boundaryCorrectedFluxCutoffPairingDensity_affineBilinear
        a eta (fun y ↦ u.toFun y - h.toFun y)
          (fun y ↦ v.toFun y - ell.toFun y) u.grad v.grad g x
  have hsplit : volumeAverage (openCubeSet Q) physicalPair =
      volumeAverage (openCubeSet Q) residualPair +
        volumeAverage (openCubeSet Q) correctionA +
        volumeAverage (openCubeSet Q) correctionB := by
    unfold volumeAverage
    have hsumInt : IntegrableOn (fun x ↦ residualPair x + correctionA x)
        (openCubeSet Q) := hresidualInt.add hcorrectionAInt
    rw [show ∫ x in openCubeSet Q, physicalPair x ∂volume =
        ∫ x in openCubeSet Q,
          (residualPair x + correctionA x) + correctionB x ∂volume by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x]
    rw [integral_add hsumInt hcorrectionBInt,
      integral_add hresidualInt hcorrectionAInt]
    ring
  have hAweak := volumeAverage_boundaryCorrectedFluxCutoffPairing_eq_neg_bulk
    M L omega Q uRes hA g hweakRes hg hzeroA heta hetaCompact
      (fun x _ ↦ Set.mem_univ x)
  have hBweak := volumeAverage_boundaryCorrectedFluxCutoffPairing_eq_neg_bulk
    M L omega Q v hB (fun _ ↦ 0) hweakV hzeroL2 hzeroB heta hetaCompact
      hetaSupport
  have hcorrAEq : volumeAverage (openCubeSet Q) correctionA =
      -volumeAverage (openCubeSet Q) (fun x ↦
        eta x ^ 2 * vecDot (boundaryCorrectedFlux a uRes.grad g x)
          (v.grad x - ell.grad x)) := by
    calc
      volumeAverage (openCubeSet Q) correctionA =
          volumeAverage (openCubeSet Q)
            (boundaryCorrectedFluxCutoffPairingDensity a eta
              (fun x ↦ uRes.toFun x - hA.toFun x) uRes.grad g) := by
        apply volumeAverage_eq_of_ae_eq
        filter_upwards with x
        simp [correctionA, a, r, hA]
      _ = -volumeAverage (openCubeSet Q) (fun x ↦
          eta x ^ 2 * vecDot (boundaryCorrectedFlux a uRes.grad g x)
            (uRes.grad x - hA.grad x)) := by
        simpa only [a] using hAweak
      _ = -volumeAverage (openCubeSet Q) (fun x ↦
          eta x ^ 2 * vecDot (boundaryCorrectedFlux a uRes.grad g x)
            (v.grad x - ell.grad x)) := by
        congr 1
        apply volumeAverage_eq_of_ae_eq
        filter_upwards with x
        simp [hA, r]
  have hcorrBEq : volumeAverage (openCubeSet Q) correctionB =
      -volumeAverage (openCubeSet Q) (fun x ↦
        eta x ^ 2 * vecDot (a x • v.grad x) (u.grad x - h.grad x)) := by
    calc
      volumeAverage (openCubeSet Q) correctionB =
          volumeAverage (openCubeSet Q)
            (boundaryCorrectedFluxCutoffPairingDensity a eta
              (fun x ↦ v.toFun x - hB.toFun x) v.grad (fun _ ↦ 0)) := by
        apply volumeAverage_eq_of_ae_eq
        filter_upwards with x
        simp [correctionB, a, w, hB]
      _ = -volumeAverage (openCubeSet Q) (fun x ↦
          eta x ^ 2 * vecDot (boundaryCorrectedFlux a v.grad (fun _ ↦ 0) x)
            (v.grad x - hB.grad x)) := by
        simpa only [a] using hBweak
      _ = -volumeAverage (openCubeSet Q) (fun x ↦
          eta x ^ 2 * vecDot (a x • v.grad x) (u.grad x - h.grad x)) := by
        congr 1
        apply volumeAverage_eq_of_ae_eq
        filter_upwards with x
        simp [boundaryCorrectedFlux, hB, w]
  have hleft : volumeAverage (openCubeSet Q)
      (boundaryCorrectedFluxCutoffPairingDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
        (fun x ↦ u.toFun x - h.toFun x) u.grad g) =
      volumeAverage (openCubeSet Q) physicalPair := by
    apply volumeAverage_eq_of_ae_eq
    filter_upwards with x
    simp [physicalPair, a, w]
  rw [hleft, hsplit, hcorrAEq, hcorrBEq]
  simp only [residualPair, uRes, hRes, a]
  ring

/-- The cutoff pairing of the zero-trace affine correction is an energy
pairing.  In particular, it is removed before the finite-height product norm
and hence before the annular inverse-gap factor is introduced. -/
theorem volumeAverage_affineCorrectionPairing_eq_neg_bulk
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (v ell : H1Function (openCubeSet Q)) (p : Vec d)
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (Set.univ : Set (Vec d)) (fun x ↦ v.toFun x - ell.toFun x))
    (hell : ∀ x, ell.grad x = p)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
          (fun x ↦ v.toFun x - ell.toFun x) v.grad (fun _ ↦ 0)) =
      -volumeAverage (openCubeSet Q) (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * eta x ^ 2 *
          vecDot (v.grad x) (v.grad x - p)) := by
  let a := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  let pair : Vec d → ℝ :=
    boundaryCorrectedFluxCutoffPairingDensity a eta
      (fun x ↦ v.toFun x - ell.toFun x) v.grad (fun _ ↦ 0)
  let bulk : Vec d → ℝ := fun x ↦
    a x * eta x ^ 2 * vecDot (v.grad x) (v.grad x - p)
  have hpoint : ∀ x,
      vecDot (a x • v.grad x) (boundarySqCutoffTestGradient eta v ell x) =
        bulk x + pair x := by
    intro x
    have hsqGrad : scalarCutoffGradientField (fun y ↦ eta y ^ 2) x =
        (2 * eta x) • euclideanGradient eta x := by
      funext i
      change euclideanCoordDeriv i (fun y ↦ eta y ^ 2) x =
        (2 * eta x) * euclideanCoordDeriv i eta x
      exact euclideanCoordDeriv_sq heta i x
    have htestGrad : boundarySqCutoffTestGradient eta v ell x =
        (eta x ^ 2) • (v.grad x - p) +
          (v.toFun x - ell.toFun x) •
            scalarCutoffGradientField (fun y ↦ eta y ^ 2) x := by
      funext i
      simp only [boundarySqCutoffTestGradient, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, hell x, hsqGrad]
    rw [htestGrad, vecDot_add_right, vecDot_smul_right,
      vecDot_smul_left]
    dsimp only [pair, bulk, a, boundaryCorrectedFluxCutoffPairingDensity,
      boundaryCorrectedFlux]
    simp only [add_zero]
    rw [vecDot_smul_left]
    ring
  have hpairInt : IntegrableOn pair (openCubeSet Q) := by
    dsimp only [pair, a]
    have hzeroL2 : MemVectorL2 (openCubeSet Q) (fun _ : Vec d ↦ (0 : Vec d)) := by
      simp [MemVectorL2, volumeMeasureOn]
    exact integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
      M L omega v ell hzeroL2 heta hetaCompact
  have htest : MemVectorL2 (openCubeSet Q)
      (boundarySqCutoffTestGradient eta v ell) :=
    memVectorL2_boundarySqCutoffTestGradient_of_smooth_compact
      v ell heta hetaCompact
  have htotal : IntegrableOn (fun x ↦
      vecDot (a x • v.grad x) (boundarySqCutoffTestGradient eta v ell x))
      (openCubeSet Q) := by
    exact integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q v) htest
  have hbulkInt : IntegrableOn bulk (openCubeSet Q) := by
    have hsub := htotal.sub hpairInt
    apply hsub.congr
    filter_upwards with x
    change vecDot (a x • v.grad x)
        (boundarySqCutoffTestGradient eta v ell x) - pair x = bulk x
    rw [hpoint x]
    ring
  have hid :=
    setIntegral_boundarySqCutoffTestGradient_identity_of_localizedZeroTrace
      hweak hzero heta hetaCompact (fun x _ ↦ Set.mem_univ x)
  have hid0 : ∫ x in openCubeSet Q,
      vecDot (a x • v.grad x) (boundarySqCutoffTestGradient eta v ell x)
        ∂volume = 0 := by
    simpa [a, vecDot] using hid
  have hsum : (∫ x in openCubeSet Q, bulk x ∂volume) +
      ∫ x in openCubeSet Q, pair x ∂volume = 0 := by
    rw [← integral_add hbulkInt hpairInt]
    calc
      ∫ x in openCubeSet Q, bulk x + pair x ∂volume =
          ∫ x in openCubeSet Q,
            vecDot (a x • v.grad x)
              (boundarySqCutoffTestGradient eta v ell x) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        exact (hpoint x).symm
      _ = 0 := hid0
  unfold volumeAverage
  dsimp only [pair, bulk, a]
  rw [show ∫ x in openCubeSet Q,
      boundaryCorrectedFluxCutoffPairingDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
        (fun x ↦ v.toFun x - ell.toFun x) v.grad (fun _ ↦ 0) x ∂volume =
      -∫ x in openCubeSet Q,
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * eta x ^ 2 *
          vecDot (v.grad x) (v.grad x - p) ∂volume by linarith only [hsum]]
  ring

/-- The canonical correction pairing costs only the affine lift and affine
competitor energies.  No low-frequency norm, cutoff derivative, or radius-gap
factor survives. -/
theorem abs_volumeAverage_affineCorrectionPairing_le_localizedEnergy
    [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (v ell : H1Function (openCubeSet Q)) (p : Vec d)
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (Set.univ : Set (Vec d)) (fun x ↦ v.toFun x - ell.toFun x))
    (hell : ∀ x, ell.grad x = p)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta)
    (hetaOne : ∀ x ∈ openCubeSet Q, |eta x| ≤ 1) :
    |volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
          (fun x ↦ v.toFun x - ell.toFun x) v.grad (fun _ ↦ 0))| ≤
      (3 / 2 : ℝ) * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v +
        (1 / 2 : ℝ) * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) ell := by
  rw [volumeAverage_affineCorrectionPairing_eq_neg_bulk
    M L omega Q v ell p hweak hzero hell heta hetaCompact, abs_neg]
  have hbound := abs_volumeAverage_affineCorrectionBulk_le_energy
    M L omega Q v ell p hell heta hetaCompact hetaOne
  have hvInt := integrableOn_aCutoff_energy M L omega Q v
  have hellInt := integrableOn_aCutoff_energy M L omega Q ell
  have hpInt : IntegrableOn (fun x ↦
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq p)
      (openCubeSet Q) := by
    apply hellInt.congr_fun
    · intro x _
      simp only [hell x]
    · exact measurableSet_openCubeSet Q
  have havg : volumeAverage (openCubeSet Q) (fun x ↦
          (3 / 2 : ℝ) *
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)) +
            (1 / 2 : ℝ) *
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq p)) =
        (3 / 2 : ℝ) * volumeAverage (openCubeSet Q) (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)) +
        (1 / 2 : ℝ) * volumeAverage (openCubeSet Q) (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq p) := by
    unfold volumeAverage
    rw [integral_add (hvInt.const_mul _) (hpInt.const_mul _),
      integral_const_mul, integral_const_mul]
    ring
  calc
    |volumeAverage (openCubeSet Q) (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * eta x ^ 2 *
          vecDot (v.grad x) (v.grad x - p))| ≤
        volumeAverage (openCubeSet Q) (fun x ↦
          (3 / 2 : ℝ) *
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)) +
            (1 / 2 : ℝ) *
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq p)) := hbound
    _ = (3 / 2 : ℝ) * volumeAverage (openCubeSet Q) (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)) +
        (1 / 2 : ℝ) * volumeAverage (openCubeSet Q) (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (ell.grad x)) := by
      rw [havg]
      congr 2
      apply volumeAverage_eq_of_ae_eq
      filter_upwards with x
      simp only [hell x]
    _ = _ := by
      rw [volumeAverage_aCutoff_vecNormSq_eq_localizedCoeffEnergyValue
          M L omega Q v,
        volumeAverage_aCutoff_vecNormSq_eq_localizedCoeffEnergyValue
          M L omega Q ell]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
