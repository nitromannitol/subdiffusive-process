module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveIntegrability

@[expose] public section

/-!
# The corrected-flux form of the nonzero-datum cutoff term

The direct test by `eta^2 (u-h)` should not price
`a |u-h|^2 |grad eta|^2` pointwise.  The two cutoff cross terms combine into
the single pairing

`(a grad u + g) . ((u-h) grad (eta^2))`.

This is the form accepted by the Chapter-3 cutoff-product machinery.  The
datum and force terms remain external Young-priced errors.

PROVENANCE: this is the nonzero-datum analogue of the unsplit weak-testing
step in CoarseGraining's
`Deterministic/CoarseCaccioppoli/SingleCubeToRaw/WeakTesting.lean`.  The
decomposition mirrors `Algsuperdiff/Section4/Provider/ExcessDecay/
BoundaryOuterCaccioppoli.lean`, but retains the corrected forcing flux.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The flux which is solenoidal for the sign convention
`-div(a grad u) = div g`. -/
def boundaryCorrectedFlux (a : Vec d → ℝ) (U G : Vec d → Vec d) :
    Vec d → Vec d :=
  fun x => a x • U x + G x

/-- The full cutoff cross term, written with `grad (eta^2)` so that it is a
literal cutoff-product pairing. -/
def boundaryCorrectedFluxCutoffPairingDensity
    (a eta w : Vec d → ℝ) (U G : Vec d → Vec d) : Vec d → ℝ :=
  fun x => vecDot (boundaryCorrectedFlux a U G x)
    (w x • scalarCutoffGradientField (fun y => eta y ^ 2) x)

/-- Pointwise identification of the corrected-flux pairing with the two
cutoff terms in the expanded squared-cutoff test. -/
theorem boundaryCorrectedFluxCutoffPairingDensity_eq
    {a eta w : Vec d → ℝ} {U G : Vec d → Vec d}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (x : Vec d) :
    boundaryCorrectedFluxCutoffPairingDensity a eta w U G x =
      2 * a x * eta x * w x * vecDot (U x) (euclideanGradient eta x) +
        2 * eta x * w x * vecDot (G x) (euclideanGradient eta x) := by
  have hgrad : scalarCutoffGradientField (fun y => eta y ^ 2) x =
      (2 * eta x) • euclideanGradient eta x := by
    funext i
    change euclideanCoordDeriv i (fun y => eta y ^ 2) x =
      ((2 * eta x) • euclideanGradient eta x) i
    rw [Pi.smul_apply]
    change euclideanCoordDeriv i (fun y => eta y ^ 2) x =
      (2 * eta x) * euclideanCoordDeriv i eta x
    rw [euclideanCoordDeriv_sq heta i x]
  rw [boundaryCorrectedFluxCutoffPairingDensity, hgrad]
  rw [boundaryCorrectedFlux]
  rw [vecDot_smul_right]
  rw [vecDot_smul_right (a x • U x + G x) (euclideanGradient eta x)
    (2 * eta x)]
  rw [vecDot_add_left, vecDot_smul_left]
  ring

/-- The three non-cutoff cross terms cost one quarter of the main energy plus
the datum and inverse-coefficient force energies. -/
theorem scalar_boundary_corrected_remainder_le
    {a eta : ℝ} {U H G : Vec d} (ha : 0 < a) :
    a * eta ^ 2 * vecDot U H - eta ^ 2 * vecDot G U +
        eta ^ 2 * vecDot G H ≤
      (1 / 4 : ℝ) * (a * eta ^ 2 * vecNormSq U) +
        (5 / 2 : ℝ) * (a * eta ^ 2 * vecNormSq H) +
        (5 / 2 : ℝ) * (a⁻¹ * eta ^ 2 * vecNormSq G) := by
  let r : ℝ := Real.sqrt a
  have hr : 0 < r := Real.sqrt_pos.2 ha
  have hr0 : r ≠ 0 := hr.ne'
  have hrsq : r ^ 2 = a := by
    dsimp [r]
    exact Real.sq_sqrt ha.le
  have hrmul : r * r = a := by simpa [pow_two] using hrsq
  have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0
  have hUHraw :=
    abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (r * eta / 2) (2 * r * eta) U H
  have hUH :
      |a * eta ^ 2 * vecDot U H| ≤
        (a * eta ^ 2 * vecNormSq U) / 8 +
          2 * a * eta ^ 2 * vecNormSq H := by
    calc
      |a * eta ^ 2 * vecDot U H| =
          |(r * eta / 2) * (2 * r * eta) * vecDot U H| := by
        congr 1
        rw [← hrmul]
        ring
      _ ≤ _ := hUHraw
      _ = _ := by rw [← hrsq]; ring
  have hGUraw :=
    abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (r * eta / 2) (2 * eta * r⁻¹) U G
  have hGU :
      |eta ^ 2 * vecDot G U| ≤
        (a * eta ^ 2 * vecNormSq U) / 8 +
          2 * a⁻¹ * eta ^ 2 * vecNormSq G := by
    rw [vecDot_comm]
    calc
      |eta ^ 2 * vecDot U G| =
          |(r * eta / 2) * (2 * eta * r⁻¹) * vecDot U G| := by
        congr 1
        rw [show r * eta / 2 * (2 * eta * r⁻¹) = eta ^ 2 by
          calc
            r * eta / 2 * (2 * eta * r⁻¹) = (r * r⁻¹) * eta ^ 2 := by ring
            _ = eta ^ 2 := by rw [hinv, one_mul]]
      _ ≤ _ := hGUraw
      _ = _ := by rw [← hrsq]; field_simp [hr0]; ring
  have hGHraw :=
    abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (r * eta) (eta * r⁻¹) H G
  have hGH :
      |eta ^ 2 * vecDot G H| ≤
        (a * eta ^ 2 * vecNormSq H) / 2 +
          (a⁻¹ * eta ^ 2 * vecNormSq G) / 2 := by
    rw [vecDot_comm]
    calc
      |eta ^ 2 * vecDot H G| =
          |(r * eta) * (eta * r⁻¹) * vecDot H G| := by
        congr 1
        rw [show (r * eta) * (eta * r⁻¹) = eta ^ 2 by
          calc
            (r * eta) * (eta * r⁻¹) = (r * r⁻¹) * eta ^ 2 := by ring
            _ = eta ^ 2 := by rw [hinv, one_mul]]
      _ ≤ _ := hGHraw
      _ = _ := by rw [← hrsq]; field_simp [hr0]
  have hUH' := (le_abs_self (a * eta ^ 2 * vecDot U H)).trans hUH
  have hGU' := (neg_le_abs (eta ^ 2 * vecDot G U)).trans hGU
  have hGH' := (le_abs_self (eta ^ 2 * vecDot G H)).trans hGH
  linarith only [hUH', hGU', hGH']

/-- The expanded direct-test RHS plus the corrected-flux pairing contains
only the three non-cutoff cross terms. -/
theorem boundaryCoerciveRhsDensity_add_correctedFluxPairing
    {a eta w : Vec d → ℝ} {U H G : Vec d → Vec d}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (x : Vec d) :
    boundaryCoerciveRhsDensity a eta w U H G x +
        boundaryCorrectedFluxCutoffPairingDensity a eta w U G x =
      a x * eta x ^ 2 * vecDot (U x) (H x) -
        eta x ^ 2 * vecDot (G x) (U x) +
        eta x ^ 2 * vecDot (G x) (H x) := by
  rw [boundaryCorrectedFluxCutoffPairingDensity_eq heta]
  simp only [boundaryCoerciveRhsDensity]
  ring

/-- Pointwise corrected-flux form of the direct coercive estimate. -/
theorem boundaryCoerciveRhsDensity_add_correctedFluxPairing_le
    {a eta w : Vec d → ℝ} {U H G : Vec d → Vec d}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) {x : Vec d} (ha : 0 < a x) :
    boundaryCoerciveRhsDensity a eta w U H G x +
        boundaryCorrectedFluxCutoffPairingDensity a eta w U G x ≤
      (1 / 4 : ℝ) * boundaryCoerciveMainDensity a eta U x +
        (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta H x +
        (5 / 2 : ℝ) * boundaryCoerciveForceDensity a eta G x := by
  rw [boundaryCoerciveRhsDensity_add_correctedFluxPairing heta]
  exact scalar_boundary_corrected_remainder_le ha

/-- Integrated corrected-flux coercivity.  Unlike the crude direct estimate,
this result leaves no positive coefficient-weighted cutoff density: its only
cutoff term is the absolute integral of the corrected-flux pairing. -/
theorem setIntegral_boundaryCoerciveMain_le_correctedFluxPairing_of_weak_identity
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
    ∫ x in openCubeSet Q, boundaryCoerciveMainDensity a eta u.grad x ∂volume ≤
      (1 / 4 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveMainDensity a eta u.grad x ∂volume +
        (5 / 2 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveDatumDensity a eta h.grad x ∂volume +
        (5 / 2 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveForceDensity a eta g x ∂volume +
        |∫ x in openCubeSet Q,
          boundaryCorrectedFluxCutoffPairingDensity a eta
            (fun y => u.toFun y - h.toFun y) u.grad g x ∂volume| := by
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
          simpa only [Pi.add_apply] using
            (integral_add ((hmain.const_mul _).add (hdatum.const_mul _))
              (hforce.const_mul _))
      _ = ((∫ x in openCubeSet Q,
              (1 / 4 : ℝ) * boundaryCoerciveMainDensity a eta u.grad x ∂volume) +
            ∫ x in openCubeSet Q,
              (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta h.grad x ∂volume) +
            ∫ x in openCubeSet Q,
              (5 / 2 : ℝ) * boundaryCoerciveForceDensity a eta g x ∂volume := by
          rw [show
            ∫ x in openCubeSet Q,
                ((1 / 4 : ℝ) * boundaryCoerciveMainDensity a eta u.grad x +
                  (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta h.grad x) ∂volume =
              (∫ x in openCubeSet Q,
                  (1 / 4 : ℝ) * boundaryCoerciveMainDensity a eta u.grad x ∂volume) +
                ∫ x in openCubeSet Q,
                  (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta h.grad x ∂volume by
            simpa only [Pi.add_apply] using
              (integral_add (hmain.const_mul _) (hdatum.const_mul _))]
      _ = _ := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hboundEq] at hmono
  have hnegPair :
      -(∫ x in openCubeSet Q,
          boundaryCorrectedFluxCutoffPairingDensity a eta w u.grad g x ∂volume) ≤
        |∫ x in openCubeSet Q,
          boundaryCorrectedFluxCutoffPairingDensity a eta w u.grad g x ∂volume| :=
    neg_le_abs _
  dsimp only [w] at hid hmono hnegPair ⊢
  linarith only [hid, hmono, hnegPair]

/-- Square-integrability of the corrected physical flux. -/
theorem memVectorL2_boundaryCorrectedFlux_aCutoff
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} (u : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g) :
    MemVectorL2 (openCubeSet Q)
      (boundaryCorrectedFlux (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        u.grad g) := by
  exact (memVectorL2_aCutoff_smul_grad M L omega Q u).add hg



theorem memVectorL2_sub_mul_scalarCutoffGradientField_sq
    {Q : TriadicCube d} (u h : H1Function (openCubeSet Q))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    MemVectorL2 (openCubeSet Q) (fun x =>
      (u.toFun x - h.toFun x) •
        scalarCutoffGradientField (fun y => eta y ^ 2) x) := by
  let w : H1Function (openCubeSet Q) := u - h
  have hetaSq : ContDiff ℝ (⊤ : ℕ∞) (fun y => eta y ^ 2) := heta.pow 2
  have hetaSqCompact : HasCompactSupport (fun y => eta y ^ 2) := by
    simpa only [Pi.mul_apply, pow_two] using! hetaCompact.mul_left (f := eta)
  have hmem : MemVectorL2 (openCubeSet Q) (fun x =>
      w.toFun x • scalarCutoffGradientField (fun y => eta y ^ 2) x) := by
    simpa [MemVectorL2, volumeMeasureOn, Pi.smul_apply, smul_eq_mul, mul_comm] using
      (MemLp.of_eval fun i : Fin d => by
        have hgradCompact : HasCompactSupport
            (fun x => scalarCutoffGradientField (fun y => eta y ^ 2) x i) := by
          simpa [scalarCutoffGradientField] using
            hetaSqCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
        rcases memH1_mul_of_contDiff_hasCompactSupport
            (contDiff_scalarCutoffGradientField_component hetaSq i) hgradCompact
            w.memH1 with ⟨v, hv⟩
        simpa [hv, mul_comm] using v.memL2)
  simpa only [w, H1Function.sub_toFun] using hmem

/-- Integrability of the literal corrected-flux cutoff pairing for `aCutoff`.
No pointwise coefficient cap enters this statement. -/
theorem integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} (u h : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    IntegrableOn
      (boundaryCorrectedFluxCutoffPairingDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
        (fun y => u.toFun y - h.toFun y) u.grad g) (openCubeSet Q) := by
  exact integrableOn_vecDot_of_memVectorL2
    (memVectorL2_boundaryCorrectedFlux_aCutoff M L omega u hg)
    (memVectorL2_sub_mul_scalarCutoffGradientField_sq u h heta hetaCompact)

/-- The explicit squared-cutoff test gradient is square integrable without a
global trace hypothesis.  Trace is needed for admissibility, not for this
analytic fact. -/
theorem memVectorL2_boundarySqCutoffTestGradient_of_smooth_compact
    {Q : TriadicCube d} (u h : H1Function (openCubeSet Q))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    MemVectorL2 (openCubeSet Q) (boundarySqCutoffTestGradient eta u h) := by
  let etaSq : Vec d → ℝ := fun x => eta x ^ 2
  have hetaSq : ContDiff ℝ (⊤ : ℕ∞) etaSq := heta.pow 2
  have hetaSqCompact : HasCompactSupport etaSq := by
    dsimp only [etaSq]
    simpa only [Pi.mul_apply, pow_two] using! hetaCompact.mul_left (f := eta)
  let w : H1Function (openCubeSet Q) := u - h
  let psi := w.mulContDiffHasCompactSupport hetaSq hetaSqCompact
  have hpsiGrad : psi.grad = boundarySqCutoffTestGradient eta u h := by
    funext x i
    rw [show psi = w.mulContDiffHasCompactSupport hetaSq hetaSqCompact by rfl,
      H1Function.mulContDiffHasCompactSupport_grad]
    change eta x ^ 2 * w.grad x i + w.toFun x *
        (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) = _
    rw [show (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) =
        2 * eta x * euclideanGradient eta x i by
      simpa [euclideanGradient, euclideanCoordDeriv] using! euclideanCoordDeriv_sq heta i x]
    simp only [w, H1Function.sub_grad, H1Function.sub_toFun]
    rfl
  simpa only [hpsiGrad] using psi.grad_memVectorL2

/-- Localized-trace direct coercivity in corrected-flux form, with all
measure-theoretic premises discharged for the GMC cutoff. -/
theorem setIntegral_aCutoff_boundaryCoerciveMain_le_correctedFluxPairing_of_localizedZeroTrace
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
      (1 / 4 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad x ∂volume +
        (5 / 2 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta h.grad x ∂volume +
        (5 / 2 : ℝ) * ∫ x in openCubeSet Q,
          boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g x ∂volume +
        |∫ x in openCubeSet Q,
          boundaryCorrectedFluxCutoffPairingDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
            (fun y => u.toFun y - h.toFun y) u.grad g x ∂volume| := by
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
    simpa only [a] using
      integrableOn_aCutoff_boundaryCoerciveForceDensity M L omega hg heta hetaCompact
  have hweakLeft : IntegrableOn
      (boundaryCoerciveWeakLeftDensity a eta w u.grad h.grad)
      (openCubeSet Q) := by
    have hpair := integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q u) htest
    simpa only [a, boundaryCoerciveWeakLeftDensity,
      boundarySqCutoffTestGradient, w] using! hpair
  have hweakForce : IntegrableOn
      (boundaryCoerciveWeakForceDensity eta w u.grad h.grad g)
      (openCubeSet Q) := by
    have hpair := integrableOn_vecDot_of_memVectorL2 hg htest
    simpa only [boundaryCoerciveWeakForceDensity,
      boundarySqCutoffTestGradient, w] using! hpair
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
    simpa only [a, w] using
      integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
        M L omega u h hg heta hetaCompact
  have hweakIdentity :=
    setIntegral_boundarySqCutoffTestGradient_identity_of_localizedZeroTrace
      hweak hzero heta hetaCompact hetaSupport
  apply setIntegral_boundaryCoerciveMain_le_correctedFluxPairing_of_weak_identity
    heta (fun x _ => SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x)
    hmain hweakLeft hweakForce hrhs hdatum hforce hpair
  simpa only [a, boundaryCoerciveWeakLeftDensity,
    boundaryCoerciveWeakForceDensity, boundarySqCutoffTestGradient, w] using!
      hweakIdentity

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
