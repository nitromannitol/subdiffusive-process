import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCombinedSignedHalfStep

/-!
# Physical carrier for the signed boundary product

The finite-height product must see the physical difference `u - h`, not the
affine residual `(u - v) - (h - ell)`.  Their difference `v - ell` is a
zero-trace weak test and is priced here before any inverse gap factor is
introduced.

PROVENANCE: this is the affine split used before the boundary product in
`Algsuperdiff/Section4/Provider/ExcessDecay/AffineSplitHarmonic.lean` and
`BoundaryOuterAssembly.lean`, specialized to the scalar GMC coefficient.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open Homogenization.WeakPoissonEquationOn
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Pointwise Young price for the correction produced when the value factor
of the combined signed product is changed from the affine residual to the
physical difference.  Every correction term is a cutoff energy; in
particular no cutoff derivative or radius-gap factor occurs. -/
theorem abs_combinedAffineCorrectionBulk_le_cutoffEnergy
    {a eta : ℝ} {U V P G : Vec d} (ha : 0 < a) :
    |eta ^ 2 * vecDot (a • (U + V) + G) (V - P)| ≤
      (1 / 8 : ℝ) * (a * eta ^ 2 * vecNormSq U) +
        7 * (a * eta ^ 2 * vecNormSq V) +
        6 * (a * eta ^ 2 * vecNormSq P) +
        (1 / 2 : ℝ) * (a⁻¹ * eta ^ 2 * vecNormSq G) := by
  let r := Real.sqrt a
  let W := V - P
  have hr : 0 < r := Real.sqrt_pos.2 ha
  have hr0 : r ≠ 0 := hr.ne'
  have hrsq : r ^ 2 = a := Real.sq_sqrt ha.le
  have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0
  have hinvsq : (r⁻¹) ^ 2 = a⁻¹ := by rw [inv_pow, hrsq]
  have hUraw := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    (r * eta / 2) (2 * r * eta) U W
  have hU : |a * eta ^ 2 * vecDot U W| ≤
      (1 / 8 : ℝ) * (a * eta ^ 2 * vecNormSq U) +
        2 * (a * eta ^ 2 * vecNormSq W) := by
    calc
      |a * eta ^ 2 * vecDot U W| =
          |(r * eta / 2) * (2 * r * eta) * vecDot U W| := by
        congr 1
        rw [← hrsq]
        ring
      _ ≤ _ := hUraw
      _ = _ := by rw [← hrsq]; ring
  have hVraw := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    (r * eta) (r * eta) V W
  have hV : |a * eta ^ 2 * vecDot V W| ≤
      (1 / 2 : ℝ) * (a * eta ^ 2 * vecNormSq V) +
        (1 / 2 : ℝ) * (a * eta ^ 2 * vecNormSq W) := by
    calc
      |a * eta ^ 2 * vecDot V W| =
          |(r * eta) * (r * eta) * vecDot V W| := by
        congr 1
        rw [← hrsq]
        ring
      _ ≤ _ := hVraw
      _ = _ := by rw [← hrsq]; ring
  have hGraw := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    (eta * r⁻¹) (eta * r) G W
  have hG : |eta ^ 2 * vecDot G W| ≤
      (1 / 2 : ℝ) * (a⁻¹ * eta ^ 2 * vecNormSq G) +
        (1 / 2 : ℝ) * (a * eta ^ 2 * vecNormSq W) := by
    calc
      |eta ^ 2 * vecDot G W| =
          |(eta * r⁻¹) * (eta * r) * vecDot G W| := by
        congr 1
        rw [show (eta * r⁻¹) * (eta * r) = eta ^ 2 by
          calc
            (eta * r⁻¹) * (eta * r) = (r * r⁻¹) * eta ^ 2 := by ring
            _ = eta ^ 2 := by rw [hinv, one_mul]]
      _ ≤ _ := hGraw
      _ = _ := by
        simp only [mul_pow]
        rw [hinvsq, ← hrsq]
        ring
  have hW := vecNormSq_sub_le V P
  have haeta : 0 ≤ a * eta ^ 2 := mul_nonneg ha.le (sq_nonneg eta)
  have hWscaled : a * eta ^ 2 * vecNormSq W ≤
      2 * (a * eta ^ 2 * vecNormSq V) +
        2 * (a * eta ^ 2 * vecNormSq P) := by
    have := mul_le_mul_of_nonneg_left hW haeta
    dsimp only [W] at this ⊢
    nlinarith only [this]
  have hsplit :
      |eta ^ 2 * vecDot (a • (U + V) + G) W| ≤
        |a * eta ^ 2 * vecDot U W| +
          |a * eta ^ 2 * vecDot V W| + |eta ^ 2 * vecDot G W| := by
    calc
      |eta ^ 2 * vecDot (a • (U + V) + G) W| =
          |a * eta ^ 2 * vecDot U W +
            a * eta ^ 2 * vecDot V W + eta ^ 2 * vecDot G W| := by
        congr 1
        simp only [vecDot_add_left, vecDot_smul_left]
        ring
      _ ≤ |a * eta ^ 2 * vecDot U W +
              a * eta ^ 2 * vecDot V W| +
          |eta ^ 2 * vecDot G W| := abs_add_le _ _
      _ ≤ _ := by
        have := abs_add_le (a * eta ^ 2 * vecDot U W)
          (a * eta ^ 2 * vecDot V W)
        linarith only [this]
  dsimp only [W] at hsplit ⊢
  have hV0 : 0 ≤ a * eta ^ 2 * vecNormSq V :=
    mul_nonneg haeta (vecNormSq_nonneg V)
  linarith only [hsplit, hU, hV, hG, hWscaled, hV0]

omit [NeZero d] in
/-- The zero-trace affine correction is removed at the averaged weak-energy
level.  The lift, affine datum, and force costs are outside every
finite-height and inverse-gap carrier. -/
theorem abs_volumeAverage_combinedAffineCorrectionPairing_le_cutoffEnergy
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u v ell : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
    (hweak : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) (u + v) g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (Set.univ : Set (Vec d)) (fun x ↦ v.toFun x - ell.toFun x))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    |volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          (fun x ↦ v.toFun x - ell.toFun x) (u + v).grad g)| ≤
      (1 / 8 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
        7 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
        6 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta ell.grad) +
        (1 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g) := by
  let q : H1Function (openCubeSet Q) := u + v
  let hq : H1Function (openCubeSet Q) := u + ell
  let bulk : Vec d → ℝ := fun x ↦
    eta x ^ 2 * vecDot
      (boundaryCorrectedFlux
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) q.grad g x)
      (v.grad x - ell.grad x)
  let R : Vec d → ℝ := fun x ↦
    (1 / 8 : ℝ) * boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad x +
      7 * boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad x +
      6 * boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta ell.grad x +
      (1 / 2 : ℝ) * boundaryCoerciveForceDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g x
  have hzeroQ : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (Set.univ : Set (Vec d)) (fun x ↦ q.toFun x - hq.toFun x) := by
    exact Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun x ↦ by simp [q, hq]) hzero
  have hweakEq := volumeAverage_boundaryCorrectedFluxCutoffPairing_eq_neg_bulk
    M L omega Q q hq g (by simpa only [q] using hweak) hg hzeroQ
      heta hetaCompact (fun x _ ↦ Set.mem_univ x)
  have hvalueEq : (fun x ↦ q.toFun x - hq.toFun x) =
      fun x ↦ v.toFun x - ell.toFun x := by
    funext x
    simp [q, hq]
  have hgradEq : (fun x ↦ q.grad x - hq.grad x) =
      fun x ↦ v.grad x - ell.grad x := by
    funext x
    simp [q, hq]
  have hpairEq : volumeAverage (openCubeSet Q)
      (boundaryCorrectedFluxCutoffPairingDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
        (fun x ↦ v.toFun x - ell.toFun x) (u + v).grad g) =
      -volumeAverage (openCubeSet Q) bulk := by
    have hpairFun :
        boundaryCorrectedFluxCutoffPairingDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
            (fun x ↦ q.toFun x - hq.toFun x) q.grad g =
          boundaryCorrectedFluxCutoffPairingDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
            (fun x ↦ v.toFun x - ell.toFun x) q.grad g := by
      rw [hvalueEq]
    have hbulkFun : (fun x ↦
        eta x ^ 2 * vecDot
          (boundaryCorrectedFlux
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) q.grad g x)
          (q.grad x - hq.grad x)) = bulk := by
      funext x
      rw [congrFun hgradEq x]
    rw [hpairFun, hbulkFun] at hweakEq
    simpa only [q, H1Function.add_grad] using hweakEq
  have huInt : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega u.grad_memVectorL2
        heta hetaCompact
  have hvInt : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega v.grad_memVectorL2
        heta hetaCompact
  have hellInt : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta ell.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega ell.grad_memVectorL2
        heta hetaCompact
  have hgInt := integrableOn_aCutoff_boundaryCoerciveForceDensity
    M L omega hg heta hetaCompact
  have hRInt : IntegrableOn R (openCubeSet Q) := by
    dsimp only [R]
    exact (((huInt.const_mul (1 / 8 : ℝ)).add (hvInt.const_mul 7)).add
      (hellInt.const_mul 6)).add (hgInt.const_mul (1 / 2 : ℝ))
  have hetaSqCont : Continuous (fun x ↦ eta x ^ 2) := (heta.pow 2).continuous
  have hetaSqCompact : HasCompactSupport (fun x ↦ eta x ^ 2) := by
    simpa only [pow_two] using hetaCompact.mul_left (f := eta)
  have hbulkBase : IntegrableOn (fun x ↦
      vecDot
        (boundaryCorrectedFlux
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) q.grad g x)
        (v.grad x - ell.grad x)) (openCubeSet Q) := by
    exact integrableOn_vecDot_of_memVectorL2
      ((memVectorL2_aCutoff_smul_grad M L omega Q q).add hg)
      (v.grad_memVectorL2.sub ell.grad_memVectorL2)
  have hbulkInt : IntegrableOn bulk (openCubeSet Q) := by
    exact integrableOn_mul_left_of_continuous_hasCompactSupport
      hetaSqCont hetaSqCompact hbulkBase
  have hpoint : ∀ x ∈ openCubeSet Q, |bulk x| ≤ R x := by
    intro x _hx
    dsimp only [bulk, R, q, boundaryCorrectedFlux,
      boundaryCoerciveMainDensity, boundaryCoerciveForceDensity]
    simpa only [H1Function.add_grad] using
      abs_combinedAffineCorrectionBulk_le_cutoffEnergy
        (d := d) (U := u.grad x) (V := v.grad x) (P := ell.grad x)
        (G := g x) (eta := eta x)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x)
  have habsIntegral : |∫ x in openCubeSet Q, bulk x ∂volume| ≤
      ∫ x in openCubeSet Q, |bulk x| ∂volume := abs_integral_le_integral_abs
  have hmono : (∫ x in openCubeSet Q, |bulk x| ∂volume) ≤
      ∫ x in openCubeSet Q, R x ∂volume :=
    setIntegral_mono_on hbulkInt.abs hRInt (measurableSet_openCubeSet Q) hpoint
  rw [hpairEq, abs_neg]
  have havg : |volumeAverage (openCubeSet Q) bulk| ≤
      volumeAverage (openCubeSet Q) R := by
    unfold volumeAverage
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)]
    exact mul_le_mul_of_nonneg_left (habsIntegral.trans hmono)
      (inv_nonneg.mpr ENNReal.toReal_nonneg)
  have hRavg : volumeAverage (openCubeSet Q) R =
      (1 / 8 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
        7 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
        6 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta ell.grad) +
        (1 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g) := by
    let fU := boundaryCoerciveMainDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad
    let fV := boundaryCoerciveMainDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad
    let fE := boundaryCoerciveMainDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta ell.grad
    let fG := boundaryCoerciveForceDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g
    have hfun : R =
        (((1 / 8 : ℝ) • fU + (7 : ℝ) • fV) + (6 : ℝ) • fE) +
          (1 / 2 : ℝ) • fG := by
      funext x
      simp only [R, fU, fV, fE, fG, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hfU : IntegrableOn fU (openCubeSet Q) := by simpa only [fU] using huInt
    have hfV : IntegrableOn fV (openCubeSet Q) := by simpa only [fV] using hvInt
    have hfE : IntegrableOn fE (openCubeSet Q) := by simpa only [fE] using hellInt
    have hfG : IntegrableOn fG (openCubeSet Q) := by simpa only [fG] using hgInt
    rw [hfun]
    calc
      volumeAverage (openCubeSet Q)
          ((((1 / 8 : ℝ) • fU + (7 : ℝ) • fV) + (6 : ℝ) • fE) +
            (1 / 2 : ℝ) • fG) =
          volumeAverage (openCubeSet Q)
              (((1 / 8 : ℝ) • fU + (7 : ℝ) • fV) + (6 : ℝ) • fE) +
            volumeAverage (openCubeSet Q) ((1 / 2 : ℝ) • fG) :=
        volumeAverage_add
          (((hfU.const_mul (1 / 8 : ℝ)).add (hfV.const_mul (7 : ℝ))).add
            (hfE.const_mul (6 : ℝ)))
          (hfG.const_mul (1 / 2 : ℝ))
      _ = (volumeAverage (openCubeSet Q)
              ((1 / 8 : ℝ) • fU + (7 : ℝ) • fV) +
            volumeAverage (openCubeSet Q) ((6 : ℝ) • fE)) +
          volumeAverage (openCubeSet Q) ((1 / 2 : ℝ) • fG) := by
        have h := volumeAverage_add
          ((hfU.const_mul (1 / 8 : ℝ)).add (hfV.const_mul (7 : ℝ)))
          (hfE.const_mul (6 : ℝ))
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          congrArg (fun z ↦ z + volumeAverage (openCubeSet Q)
            ((1 / 2 : ℝ) • fG)) h
      _ = _ := by
        have h := volumeAverage_add (hfU.const_mul (1 / 8 : ℝ))
          (hfV.const_mul (7 : ℝ))
        have hsum : volumeAverage (openCubeSet Q)
            ((1 / 8 : ℝ) • fU + (7 : ℝ) • fV) =
              volumeAverage (openCubeSet Q) ((1 / 8 : ℝ) • fU) +
                volumeAverage (openCubeSet Q) ((7 : ℝ) • fV) := by
          simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
        have hU := volumeAverage_smul (U := openCubeSet Q) (1 / 8 : ℝ) fU
        have hV := volumeAverage_smul (U := openCubeSet Q) (7 : ℝ) fV
        have hE := volumeAverage_smul (U := openCubeSet Q) (6 : ℝ) fE
        have hG := volumeAverage_smul (U := openCubeSet Q) (1 / 2 : ℝ) fG
        dsimp only [fU, fV, fE, fG]
        dsimp only [fU, fV, fE, fG] at h hU hV hE hG
        rw [hsum, hU, hV, hE, hG]
  calc
    |volumeAverage (openCubeSet Q) bulk| ≤ volumeAverage (openCubeSet Q) R := havg
    _ = _ := hRavg

omit [NeZero d] in
/-- A scalar multiple of a zero-force weak solution is again a zero-force
weak solution.  The half multiple is the normalization used to feed the
already-landed combined-flux product with the physical carrier. -/
theorem isDivFormWeakSolutionOn_half_smul_zero
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (v : H1Function (openCubeSet Q))
    (hweak : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0)) :
    IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q)
      ((1 / 2 : ℝ) • v) (fun _ ↦ 0) := by
  intro phi
  have hv := hweak phi
  have hbase : IntegrableOn (fun x ↦
      vecDot ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
        (phi.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q v)
      phi.toH1Function.grad_memVectorL2
  have hleft : ∫ x in openCubeSet Q,
      vecDot
        ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) •
          ((1 / 2 : ℝ) • v).grad x)
        (phi.toH1Function.grad x) ∂volume =
      (1 / 2 : ℝ) * ∫ x in openCubeSet Q,
        vecDot ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
          (phi.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [H1Function.smul_grad, smul_smul, vecDot_smul_left]
    ring
  rw [hleft, hv]
  simp [vecDot]

omit [NeZero d] in
/-- Adding a zero-force weak solution preserves the right-hand side. -/
theorem isDivFormWeakSolutionOn_add_zero
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u v : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
    (hu : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g)
    (hv : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0)) :
    IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) (u + v) g := by
  intro phi
  let fu : Vec d → ℝ := fun x ↦
    vecDot ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • u.grad x)
      (phi.toH1Function.grad x)
  let fv : Vec d → ℝ := fun x ↦
    vecDot ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
      (phi.toH1Function.grad x)
  have hfu : IntegrableOn fu (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q u)
      phi.toH1Function.grad_memVectorL2
  have hfv : IntegrableOn fv (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q v)
      phi.toH1Function.grad_memVectorL2
  have hleft : ∫ x in openCubeSet Q,
      vecDot ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • (u + v).grad x)
        (phi.toH1Function.grad x) ∂volume =
      ∫ x in openCubeSet Q, fu x + fv x ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [fu, fv, H1Function.add_grad, smul_add, vecDot_add_left]
  rw [hleft, integral_add hfu hfv, hu phi, hv phi]
  simp [vecDot]

/-- The established combined finite-height theorem, normalized by a half
lift, puts the physical value `u-h` into both the finite head and the fine
gradient tail.  The lift energy is present only in the explicit energy row,
never in `boundaryCommonYoungParentBudgetWeighted`. -/
theorem exists_abs_physicalCombinedPairing_triadicGap
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE : ℝ} {g : Vec d → Vec d}
        (u v h : H1Function (openCubeSet Q)) (center : Vec d)
        {rhoInner rhoOuter : ℝ} {k : ℕ},
        IsDivFormWeakSolutionOn
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g →
        IsDivFormWeakSolutionOn
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v
            (fun _ ↦ 0) →
        0 < rhoInner → rhoInner < rhoOuter →
        CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 ≤ K →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g x) →
        MemLp (u - h).toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        MemVectorL2 (openCubeSet Q) g →
        (let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) h.grad);
          descendantsAverage Q (k + 1) Eh ≤ BE) →
        let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
        let Eu : Vec d → ℝ := fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
        let Ev : Vec d → ℝ := fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (v.grad x)
        let Eh0 : Vec d → ℝ := fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (h.grad x)
        let energy : Vec d → ℝ := fun x ↦
          Eu x + (1 / 2 : ℝ) * Ev x + (1 / 2 : ℝ) * Eh0 x
        |volumeAverage (openCubeSet Q)
            (boundaryCorrectedFluxCutoffPairingDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
              (u - h).toFun (u + v).grad g)| ≤
          (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter energy +
            4 * boundaryCommonYoungParentBudgetWeighted Q k rhoInner rhoOuter
              s sigma K C BE (u - h).toFun (fun x ↦ -g x) := by
  obtain ⟨C, hC, hcap⟩ := exists_abs_combinedSignedPairing_triadicGap d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE g u v h center rhoInner rhoOuter k
    hweakU hweakV hinner hlt hchoice hs hs4 hsigma hK hupper hlower hreg
    hphysicalL2 hgL2 hgOpen hEh
  let vHalf : H1Function (openCubeSet Q) := (1 / 2 : ℝ) • v
  have hweakHalf := isDivFormWeakSolutionOn_half_smul_zero
    M L omega Q v hweakV
  have hraw := hcap M L omega u vHalf h center hweakU hweakHalf
    hinner hlt hchoice hs hs4 hsigma hK hupper hlower hreg hphysicalL2 hgL2
      hgOpen hEh
  dsimp only
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Eu : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
  let Ev : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (v.grad x)
  let Eh0 : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (h.grad x)
  let energy : Vec d → ℝ := fun x ↦
    Eu x + (1 / 2 : ℝ) * Ev x + (1 / 2 : ℝ) * Eh0 x
  have hpairFun : boundaryCorrectedFluxCutoffPairingDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
      (u - h).toFun (u + (2 : ℝ) • vHalf).grad g =
    boundaryCorrectedFluxCutoffPairingDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
      (u - h).toFun (u + v).grad g := by
    funext x
    simp only [boundaryCorrectedFluxCutoffPairingDensity,
      boundaryCorrectedFlux, H1Function.add_grad, H1Function.smul_grad,
      vHalf, smul_smul, vecDot_add_left, vecDot_smul_left]
    ring
  have henergyFun : (fun x ↦
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x) +
        2 * (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (vHalf.grad x)) +
        (1 / 2 : ℝ) * (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (h.grad x))) = energy := by
    funext x
    dsimp only [energy, Eu, Ev, Eh0, vHalf, H1Function.smul_grad]
    simp only [vecNormSq, vecDot_smul_left, vecDot_smul_right]
    ring
  dsimp only [vHalf] at hraw
  rw [hpairFun, henergyFun] at hraw
  simpa only [eta, Eu, Ev, Eh0, energy] using hraw

/-- Carrier replacement for the signed affine residual.  The
finite-height/gap term sees the physical value `u-h`; the discrepancy
`v-ell` is a zero-trace weak test and appears only through the four displayed
cutoff energies. -/
theorem exists_abs_affineResidualCombinedPairing_physicalCarrier_triadicGap
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE : ℝ} {g : Vec d → Vec d}
        (u h v ell : H1Function (openCubeSet Q)) (center : Vec d)
        {rhoInner rhoOuter : ℝ} {k : ℕ},
        IsDivFormWeakSolutionOn
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g →
        IsDivFormWeakSolutionOn
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v
            (fun _ ↦ 0) →
        MemVectorL2 (openCubeSet Q) g →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (Set.univ : Set (Vec d)) (fun x ↦ v.toFun x - ell.toFun x) →
        0 < rhoInner → rhoInner < rhoOuter →
        CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 ≤ K →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g x) →
        MemLp (u - h).toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        (let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) h.grad);
          descendantsAverage Q (k + 1) Eh ≤ BE) →
        let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
        let Eu : Vec d → ℝ := fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
        let Ev : Vec d → ℝ := fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (v.grad x)
        let Eh0 : Vec d → ℝ := fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (h.grad x)
        let energy : Vec d → ℝ := fun x ↦
          Eu x + (1 / 2 : ℝ) * Ev x + (1 / 2 : ℝ) * Eh0 x
        |volumeAverage (openCubeSet Q)
            (boundaryCorrectedFluxCutoffPairingDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
              ((u - v) - (h - ell)).toFun ((u - v) + (2 : ℝ) • v).grad g)| ≤
          (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter energy +
            4 * boundaryCommonYoungParentBudgetWeighted Q k rhoInner rhoOuter
              s sigma K C BE (u - h).toFun (fun x ↦ -g x) +
            (1 / 8 : ℝ) * volumeAverage (openCubeSet Q)
              (boundaryCoerciveMainDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) +
            7 * volumeAverage (openCubeSet Q)
              (boundaryCoerciveMainDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) +
            6 * volumeAverage (openCubeSet Q)
              (boundaryCoerciveMainDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta ell.grad) +
            (1 / 2 : ℝ) * volumeAverage (openCubeSet Q)
              (boundaryCoerciveForceDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g) := by
  obtain ⟨C, hC, hphysical⟩ := exists_abs_physicalCombinedPairing_triadicGap d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE g u h v ell center rhoInner rhoOuter k
    hweakU hweakV hg hzero hinner hlt hchoice hs hs4 hsigma hK hupper hlower
    hreg hphysicalL2 hgL2 hEh
  dsimp only
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let Eu : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
  let Ev : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (v.grad x)
  let Eh0 : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (h.grad x)
  let energy : Vec d → ℝ := fun x ↦
    Eu x + (1 / 2 : ℝ) * Ev x + (1 / 2 : ℝ) * Eh0 x
  let q : H1Function (openCubeSet Q) := u + v
  let pairPhysical : Vec d → ℝ :=
    boundaryCorrectedFluxCutoffPairingDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
      (u - h).toFun q.grad g
  let pairCorrection : Vec d → ℝ :=
    boundaryCorrectedFluxCutoffPairingDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
      (fun x ↦ v.toFun x - ell.toFun x) q.grad g
  let pairResidual : Vec d → ℝ :=
    boundaryCorrectedFluxCutoffPairingDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
      ((u - v) - (h - ell)).toFun ((u - v) + (2 : ℝ) • v).grad g
  have hqWeak : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) q g := by
    simpa only [q] using
      isDivFormWeakSolutionOn_add_zero M L omega Q u v g hweakU hweakV
  have hphys := hphysical M L omega u v h center hweakU hweakV hinner hlt
    hchoice hs hs4 hsigma hK hupper hlower hreg hphysicalL2 hgL2 hg hEh
  have hcorr := abs_volumeAverage_combinedAffineCorrectionPairing_le_cutoffEnergy
    M L omega Q u v ell g (by simpa only [q] using hqWeak) hg hzero
      (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1)
      (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1)
  have hpairPoint : pairResidual = pairPhysical - pairCorrection := by
    have hvalue : ((u - v) - (h - ell)).toFun =
        fun x ↦ (u - h).toFun x - (v.toFun x - ell.toFun x) := by
      funext x
      simp only [H1Function.sub_toFun]
      ring
    have hflux : ((u - v) + (2 : ℝ) • v).grad = q.grad := by
      funext x i
      simp only [q, H1Function.sub_grad, H1Function.add_grad,
        H1Function.smul_grad, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    funext x
    dsimp only [pairResidual]
    rw [hvalue, hflux]
    dsimp only [pairPhysical, pairCorrection]
    simp only [boundaryCorrectedFluxCutoffPairingDensity,
      Pi.sub_apply, vecDot_smul_right]
    ring
  have hphysicalInt : IntegrableOn pairPhysical (openCubeSet Q) := by
    let datum : H1Function (openCubeSet Q) := q - (u - h)
    have hraw := integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
      M L omega q datum hg
        (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner
          (coarseCaccioppoliBufferedCutoffRadius_between hlt).1)
        (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner
          (coarseCaccioppoliBufferedCutoffRadius_between hlt).1)
    have hval : (fun y ↦ q.toFun y - datum.toFun y) = (u - h).toFun := by
      funext y
      simp only [q, datum, H1Function.sub_toFun, H1Function.add_toFun]
      ring
    rw [hval] at hraw
    simpa only [pairPhysical, eta] using hraw
  have hcorrectionInt : IntegrableOn pairCorrection (openCubeSet Q) := by
    let datum : H1Function (openCubeSet Q) := q - (v - ell)
    have hraw := integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
      M L omega q datum hg
        (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner
          (coarseCaccioppoliBufferedCutoffRadius_between hlt).1)
        (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner
          (coarseCaccioppoliBufferedCutoffRadius_between hlt).1)
    have hval : (fun y ↦ q.toFun y - datum.toFun y) =
        fun y ↦ v.toFun y - ell.toFun y := by
      funext y
      simp only [q, datum, H1Function.sub_toFun, H1Function.add_toFun]
      ring
    rw [hval] at hraw
    simpa only [pairCorrection, eta] using hraw
  have hpairAverage : volumeAverage (openCubeSet Q) pairResidual =
      volumeAverage (openCubeSet Q) pairPhysical -
        volumeAverage (openCubeSet Q) pairCorrection := by
    rw [hpairPoint, volumeAverage_sub hphysicalInt hcorrectionInt]
  have habs : |volumeAverage (openCubeSet Q) pairResidual| ≤
      |volumeAverage (openCubeSet Q) pairPhysical| +
        |volumeAverage (openCubeSet Q) pairCorrection| := by
    rw [hpairAverage]
    exact abs_sub _ _
  dsimp only [eta, Eu, Ev, Eh0, energy, q, pairPhysical,
    pairCorrection, pairResidual] at hphys hcorr habs ⊢
  linarith only [habs, hphys, hcorr]

omit [NeZero d] in


theorem boundaryCrossScale_physical_le_of_combinedSignedPairingBudget
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u r v hRes : H1Function (openCubeSet Q))
    (g : Vec d → Vec d) (center : Vec d) {rhoInner rhoOuter PairBudget Ag : ℝ}
    (hgrad : ∀ x, u.grad x = r.grad x + v.grad x)
    (hweakR : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) r g)
    (hweakV : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube Q center 1)
      (fun x ↦ r.toFun x - hRes.toFun x))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter) (houter : rhoOuter < 1)
    (hforce : volumeAverage (openCubeSet Q)
      (boundaryCoerciveForceDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g) ≤ Ag)
    (hpair : |volumeAverage (openCubeSet Q)
      (boundaryCorrectedFluxCutoffPairingDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
        (r - hRes).toFun (r + (2 : ℝ) • v).grad g)| ≤ PairBudget) :
    boundaryCrossScaleEnergyProfile Q Q center rhoInner (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (r.grad x)) +
        2 * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (v.grad x)) +
        (7 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (hRes.grad x)) +
        (5 / 2 : ℝ) * Ag + PairBudget := by
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
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (r.grad x)
  let Ev : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (v.grad x)
  let Eh : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (hRes.grad x)
  let pairR := boundaryCorrectedFluxCutoffPairingDensity
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
    (r - hRes).toFun r.grad g
  let pairV := boundaryCorrectedFluxCutoffPairingDensity
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
    (r - hRes).toFun v.grad (fun _ ↦ 0)
  let pairC := boundaryCorrectedFluxCutoffPairingDensity
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
    (r - hRes).toFun (r + (2 : ℝ) • v).grad g
  have hpairRInt : IntegrableOn pairR (openCubeSet Q) := by
    simpa only [pairR, H1Function.sub_toFun] using
      integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
        M L omega r hRes hg heta hetaCompact
  have hzeroL2 : MemVectorL2 (openCubeSet Q) (fun _ : Vec d ↦ (0 : Vec d)) := by
    simp [MemVectorL2, volumeMeasureOn]
  have hpairVInt : IntegrableOn pairV (openCubeSet Q) := by
    let datum : H1Function (openCubeSet Q) := v - (r - hRes)
    have hraw := integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
      M L omega v datum hzeroL2 heta hetaCompact
    have hval : (fun x ↦ v.toFun x - datum.toFun x) = (r - hRes).toFun := by
      funext x
      simp only [datum, H1Function.sub_toFun]
      ring
    rw [hval] at hraw
    simpa only [pairV] using hraw
  have hpairEq : volumeAverage (openCubeSet Q) pairR +
      2 * volumeAverage (openCubeSet Q) pairV =
        volumeAverage (openCubeSet Q) pairC := by
    have hfun : pairR + (2 : ℝ) • pairV = pairC := by
      funext x
      simpa only [pairR, pairV, pairC, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        H1Function.add_grad, H1Function.smul_grad] using
        boundaryCorrectedFluxCutoffPairingDensity_residual_add_two_lift
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta (r - hRes).toFun
            r.grad v.grad g x
    rw [← volumeAverage_smul]
    rw [← volumeAverage_add hpairRInt (by
      simpa only [Pi.smul_apply, smul_eq_mul] using hpairVInt.const_mul 2)]
    exact volumeAverage_eq_of_ae_eq (Filter.Eventually.of_forall fun x ↦
      congrFun hfun x)
  have huInt := integrableOn_aCutoff_energy M L omega Q u
  have hrInt := integrableOn_aCutoff_energy M L omega Q r
  have hvInt := integrableOn_aCutoff_energy M L omega Q v
  have hhInt := integrableOn_aCutoff_energy M L omega Q hRes
  have hmainU : IntegrableOn (boundaryCoerciveMainDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad) (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega u.grad_memVectorL2
        heta hetaCompact
  have hmainR : IntegrableOn (boundaryCoerciveMainDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta r.grad) (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega r.grad_memVectorL2
        heta hetaCompact
  have hmainV : IntegrableOn (boundaryCoerciveMainDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta v.grad) (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega v.grad_memVectorL2
        heta hetaCompact
  have hmainH : IntegrableOn (boundaryCoerciveMainDensity
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta hRes.grad) (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega hRes.grad_memVectorL2
        heta hetaCompact
  have hinnerU := boundaryCrossScaleEnergyProfile_le_boundaryCoerciveMain
    hinner hbetween.1
    (fun x _ ↦ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
    huInt hmainU
  have houterR := volumeAverage_boundaryCoerciveMain_localCanonicalFun_le_outerProfile
    hinner hbetween.1
    (fun x _ ↦ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
    hrInt hmainR
  have houterV := volumeAverage_boundaryCoerciveMain_localCanonicalFun_le_outerProfile
    hinner hbetween.1
    (fun x _ ↦ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
    hvInt hmainV
  have houterH := volumeAverage_boundaryCoerciveMain_localCanonicalFun_le_outerProfile
    hinner hbetween.1
    (fun x _ ↦ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
    hhInt hmainH
  have hmonoR := boundaryCrossScaleEnergyProfile_mono
    (Q := Q) (R := Q) (center := center) hbetween.2.le
    (fun x _ ↦ mul_nonneg
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le (vecNormSq_nonneg _))
    hrInt
  have hmonoV := boundaryCrossScaleEnergyProfile_mono
    (Q := Q) (R := Q) (center := center) hbetween.2.le
    (fun x _ ↦ mul_nonneg
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le (vecNormSq_nonneg _))
    hvInt
  have hmonoH := boundaryCrossScaleEnergyProfile_mono
    (Q := Q) (R := Q) (center := center) hbetween.2.le
    (fun x _ ↦ mul_nonneg
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le (vecNormSq_nonneg _))
    hhInt
  have houterR' := houterR.trans hmonoR
  have houterV' := houterV.trans hmonoV
  have houterH' := houterH.trans hmonoH
  have hdatum : volumeAverage (openCubeSet Q)
      (boundaryCoerciveDatumDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta hRes.grad) ≤
      boundaryCrossScaleEnergyProfile Q Q center rhoOuter Eh := by
    simpa only [boundaryCoerciveDatumDensity, boundaryCoerciveMainDensity,
      Eh] using houterH'
  have hpairNeg : -volumeAverage (openCubeSet Q) pairC ≤ PairBudget :=
    (neg_le_abs _).trans hpair
  dsimp only [eta, Er, Ev, Eh, pairR, pairV, pairC, H1Function.sub_toFun]
    at hsigned hpairEq hinnerU houterR' houterV' hdatum hpairNeg hforce ⊢
  simp only [H1Function.sub_toFun] at hpairEq hpairNeg
  have hmainCap : volumeAverage (openCubeSet Q)
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) u.grad) ≤
      (1 / 4 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) r.grad) +
        (7 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) hRes.grad) +
        (5 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g) +
        2 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveMainDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) v.grad) +
        PairBudget := by
    linarith only [hsigned, hpairEq, hpairNeg]
  have houterCap : volumeAverage (openCubeSet Q)
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) u.grad) ≤
      (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (r.grad x)) +
        2 * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (v.grad x)) +
        (7 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (hRes.grad x)) +
        (5 / 2 : ℝ) * Ag + PairBudget := by
    linarith only [hmainCap, houterR', houterV', hdatum, hforce]
  exact hinnerU.trans houterCap

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
