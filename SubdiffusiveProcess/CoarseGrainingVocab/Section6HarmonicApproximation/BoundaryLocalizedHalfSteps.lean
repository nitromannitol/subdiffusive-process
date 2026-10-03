module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAffineGapCells
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAffineActiveCell
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAffineResidual
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCrossScaleSummation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open Homogenization.WeakPoissonEquationOn
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Joint algebra for the two affine-covariance correction bulks.  The
negative energy of `grad (v - ell)` is retained until all cross terms have
been estimated; consequently no energy of the raw affine competitor occurs
on the right-hand side. -/
theorem jointAffineCorrectionBulks_le
    (a eta : ℝ) (ha : 0 < a) (q H w v g r : Vec d)
    (hr : r = q + H - w) :
    eta ^ 2 * (vecDot (a • r + g) w + vecDot (a • v) q) ≤
      eta ^ 2 * ((a / 2) * vecNormSq q +
        2 * a * vecNormSq H + 2 * a⁻¹ * vecNormSq g +
        (3 * a / 2) * vecNormSq v) := by
  subst r
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  have hcoord : ∀ i : Fin d,
      (a * ((q + H - w) i) + g i) * w i + a * v i * q i ≤
        (a / 2) * (q i * q i) + 2 * a * (H i * H i) +
          2 * a⁻¹ * (g i * g i) + (3 * a / 2) * (v i * v i) := by
    intro i
    have hq := sq_nonneg (2 * q i - 3 * w i)
    have hH := sq_nonneg (4 * H i - w i)
    have hg := sq_nonneg (4 * g i - a * w i)
    have hv := sq_nonneg (q i - 3 * v i)
    have hginv : g i * w i ≤ 2 * a⁻¹ * g i ^ 2 + a / 8 * w i ^ 2 := by
      have hscaled := mul_nonneg (inv_nonneg.mpr ha.le) hg
      nlinarith
    have hq' : a * q i * w i ≤
        a * ((1 / 3 : ℝ) * q i ^ 2 + (3 / 4 : ℝ) * w i ^ 2) := by
      have : q i * w i ≤
          (1 / 3 : ℝ) * q i ^ 2 + (3 / 4 : ℝ) * w i ^ 2 := by
        nlinarith only [hq]
      simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left this ha.le
    have hH' : a * H i * w i ≤
        a * (2 * H i ^ 2 + (1 / 8 : ℝ) * w i ^ 2) := by
      have : H i * w i ≤ 2 * H i ^ 2 + (1 / 8 : ℝ) * w i ^ 2 := by
        nlinarith only [hH]
      simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left this ha.le
    have hv' : a * v i * q i ≤
        a * ((1 / 6 : ℝ) * q i ^ 2 + (3 / 2 : ℝ) * v i ^ 2) := by
      have : v i * q i ≤
          (1 / 6 : ℝ) * q i ^ 2 + (3 / 2 : ℝ) * v i ^ 2 := by
        nlinarith only [hv]
      simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left this ha.le
    simp only [Pi.add_apply, Pi.sub_apply]
    nlinarith only [hq', hH', hginv, hv']
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦ hcoord i
  simp only [vecDot, vecNormSq, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum] at hsum ⊢
  have heta0 : 0 ≤ eta ^ 2 := sq_nonneg eta
  exact mul_le_mul_of_nonneg_left hsum heta0

omit [NeZero d] in
/-- The preceding cancellation on the actual two weak correction bulks. -/
theorem jointAffineCorrectionBulkDensities_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} (u h v ell : H1Function (openCubeSet Q))
    (g : Vec d → Vec d) (eta : Vec d → ℝ) (x : Vec d) :
    eta x ^ 2 *
          vecDot
            (boundaryCorrectedFlux
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (u - v).grad g x)
            (v.grad x - ell.grad x) +
        eta x ^ 2 * vecDot
          ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
          (u.grad x - h.grad x) ≤
      eta x ^ 2 *
        (((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) / 2) *
            vecNormSq (u.grad x - h.grad x) +
          2 * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (h.grad x - ell.grad x) +
          2 * (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ *
            vecNormSq (g x) +
          (3 * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x / 2) *
            vecNormSq (v.grad x)) := by
  let a := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x
  have ha : 0 < a := SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x
  have hr : (u - v).grad x =
      (u.grad x - h.grad x) + (h.grad x - ell.grad x) -
        (v.grad x - ell.grad x) := by
    funext i
    simp only [H1Function.sub_grad, Pi.sub_apply, Pi.add_apply]
    ring
  have hbound := jointAffineCorrectionBulks_le
    a (eta x) ha (u.grad x - h.grad x) (h.grad x - ell.grad x)
      (v.grad x - ell.grad x) (v.grad x) (g x) ((u - v).grad x) hr
  simpa only [a, boundaryCorrectedFlux, vecDot_smul_left,
    add_mul, mul_add] using! hbound

omit [NeZero d] in
/-- Integrated joint-bulk estimate.  This keeps the signed correction pair
intact through the weak-form average instead of estimating either term by an
absolute value. -/
theorem volumeAverage_jointAffineCorrectionBulks_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q : TriadicCube d} (u h v ell : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    volumeAverage (openCubeSet Q) (fun x ↦
        eta x ^ 2 *
          vecDot
            (boundaryCorrectedFlux
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (u - v).grad g x)
            (v.grad x - ell.grad x)) +
      volumeAverage (openCubeSet Q) (fun x ↦
        eta x ^ 2 * vecDot
          ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
          (u.grad x - h.grad x)) ≤
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
  let lhs : Vec d → ℝ := fun x ↦
    eta x ^ 2 *
        vecDot
          (boundaryCorrectedFlux
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (u - v).grad g x)
          (v.grad x - ell.grad x) +
      eta x ^ 2 * vecDot
        ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
        (u.grad x - h.grad x)
  let rhs : Vec d → ℝ := fun x ↦
    eta x ^ 2 *
      (((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) / 2) *
          vecNormSq (u.grad x - h.grad x) +
        2 * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (h.grad x - ell.grad x) +
        2 * (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ *
          vecNormSq (g x) +
        (3 * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x / 2) *
          vecNormSq (v.grad x))
  have hetaCont : Continuous (fun x ↦ eta x ^ 2) := (heta.pow 2).continuous
  have hetaSupp : HasCompactSupport (fun x ↦ eta x ^ 2) := by
    simpa only [pow_two] using! hetaCompact.mul_left (f := eta)
  have hfluxRes : MemVectorL2 (openCubeSet Q)
      (boundaryCorrectedFlux (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (u - v).grad g) :=
    memVectorL2_boundaryCorrectedFlux_aCutoff M L omega (u - v) hg
  have hw : MemVectorL2 (openCubeSet Q) (fun x ↦ v.grad x - ell.grad x) := by
    simpa only [H1Function.sub_grad] using! (v - ell).grad_memVectorL2
  have hq : MemVectorL2 (openCubeSet Q) (fun x ↦ u.grad x - h.grad x) := by
    simpa only [H1Function.sub_grad] using! (u - h).grad_memVectorL2
  have hH : MemVectorL2 (openCubeSet Q) (fun x ↦ h.grad x - ell.grad x) := by
    simpa only [H1Function.sub_grad] using! (h - ell).grad_memVectorL2
  have hA0 : IntegrableOn (fun x ↦
      vecDot
        (boundaryCorrectedFlux (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (u - v).grad g x) (v.grad x - ell.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hfluxRes hw
  have hA : IntegrableOn (fun x ↦ eta x ^ 2 *
      vecDot
        (boundaryCorrectedFlux (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (u - v).grad g x) (v.grad x - ell.grad x)) (openCubeSet Q) :=
    integrableOn_mul_left_of_continuous_hasCompactSupport hetaCont hetaSupp hA0
  have hvflux := memVectorL2_aCutoff_smul_grad M L omega Q v
  have hB0 : IntegrableOn (fun x ↦
      vecDot ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
        (u.grad x - h.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hvflux hq
  have hB : IntegrableOn (fun x ↦ eta x ^ 2 *
      vecDot ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) • v.grad x)
        (u.grad x - h.grad x)) (openCubeSet Q) :=
    integrableOn_mul_left_of_continuous_hasCompactSupport hetaCont hetaSupp hB0
  have hlhs : IntegrableOn lhs (openCubeSet Q) := by
    simpa only [lhs] using! hA.add hB
  have hqEnergy := integrableOn_aCutoff_sqCutoff_vecNormSq
    M L omega hq heta hetaCompact
  have hHEnergy := integrableOn_aCutoff_sqCutoff_vecNormSq
    M L omega hH heta hetaCompact
  have hgEnergy := integrableOn_aCutoff_boundaryCoerciveForceDensity
    M L omega hg heta hetaCompact
  have hvEnergy := integrableOn_aCutoff_sqCutoff_vecNormSq
    M L omega v.grad_memVectorL2 heta hetaCompact
  have hrhs : IntegrableOn rhs (openCubeSet Q) := by
    have hq' := hqEnergy.const_mul (1 / 2 : ℝ)
    have hH' := hHEnergy.const_mul (2 : ℝ)
    have hg' := hgEnergy.const_mul (2 : ℝ)
    have hv' := hvEnergy.const_mul (3 / 2 : ℝ)
    have hsumInt : IntegrableOn (fun x ↦
        ((1 / 2 : ℝ) *
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * eta x ^ 2 *
              vecNormSq (u.grad x - h.grad x)) +
          2 * (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * eta x ^ 2 *
              vecNormSq (h.grad x - ell.grad x))) +
        2 * boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta g x +
        (3 / 2 : ℝ) *
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * eta x ^ 2 *
            vecNormSq (v.grad x))) (openCubeSet Q) :=
      ((hq'.add hH').add hg').add hv'
    apply hsumInt.congr_fun
    · intro x _hx
      simp only [rhs, boundaryCoerciveForceDensity]
      ring
    · exact measurableSet_openCubeSet Q
  rw [← volumeAverage_add hA hB]
  unfold volumeAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  exact MeasureTheory.setIntegral_mono_on hlhs hrhs (measurableSet_openCubeSet Q)
    fun x _hx ↦ jointAffineCorrectionBulkDensities_le M L omega u h v ell g eta x

omit [NeZero d] in
/-- Affine covariance with the signed correction pair already absorbed into
its coercive four-density envelope.  This is the direction needed when the
residual direct test is estimated by the physical finite-height pairing. -/
theorem volumeAverage_residualCorrectedFluxPairing_le_physical_add_jointBudget
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u h v ell : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
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
        (boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          (fun x ↦ (u - v).toFun x - (h - ell).toFun x)
          (u - v).grad g) ≤
      volumeAverage (openCubeSet Q)
          (boundaryCorrectedFluxCutoffPairingDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
            (fun x ↦ u.toFun x - h.toFun x) u.grad g) +
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
  have hcov := volumeAverage_boundaryCorrectedFluxCutoffPairing_affineCovariant
    M L omega Q u h v ell g hweakRes hweakV hg hphysical haffine
      heta hetaCompact hetaSupport
  have hbulk := volumeAverage_jointAffineCorrectionBulks_le
    M L omega u h v ell hg heta hetaCompact
  linarith only [hcov, hbulk]

/-- Full-cube coefficient-energy triangle inequality.  It is used to split
the affine-external comparison datum `h - v` into the printed boundary
fluctuation budget and the separately priced affine lift. -/
theorem localizedCoeffEnergyValue_sub_le_two_mul_add
    (Q : TriadicCube d) (a : CoeffFamily d)
    (h v : H1Function (openCubeSet Q)) :
    localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) (h - v) ≤
      2 * localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) h +
        2 * localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v := by
  have hmono : volumeMeasureOn (openCubeSet Q) ≤
      volumeMeasureOn (openCubeSet Q) := le_rfl
  have hh := h.grad_memVectorL2.mono_measure hmono
  have hv := v.grad_memVectorL2.mono_measure hmono
  have hsub := (h - v).grad_memVectorL2.mono_measure hmono
  have hsplit : (h - v).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun y ↦ h.grad y + (-v).grad y := by
    filter_upwards with y
    funext i
    simp only [H1Function.sub_grad, H1Function.neg_grad, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply]
    ring
  have htriangle :=
    volumeAverage_coefficientEnergyDensity_le_two_mul_add_of_ae_eq_add
      (V := openCubeSet Q) (A := publicCoeffField Q a)
      (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      ((publicCoeffField_isEllipticFieldOn_cubeSet Q a).mono
        (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q))
      hsub hh ((-v).grad_memVectorL2.mono_measure hmono) hsplit
  have hneg : volumeAverage (openCubeSet Q)
      (coefficientEnergyDensity (publicCoeffField Q a) (-v).grad) =
      volumeAverage (openCubeSet Q)
        (coefficientEnergyDensity (publicCoeffField Q a) v.grad) := by
    apply volumeAverage_eq_of_ae_eq
    filter_upwards with x
    unfold coefficientEnergyDensity
    simp only [H1Function.neg_grad, matVecMul_neg,
      vecDot_neg_left, vecDot_neg_right, neg_neg]
  calc
    localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) (h - v) =
        volumeAverage (openCubeSet Q)
          (coefficientEnergyDensity (publicCoeffField Q a) (h - v).grad) :=
      localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
        (Set.Subset.rfl) (h - v)
    _ ≤ 2 * volumeAverage (openCubeSet Q)
          (coefficientEnergyDensity (publicCoeffField Q a) h.grad) +
        2 * volumeAverage (openCubeSet Q)
          (coefficientEnergyDensity (publicCoeffField Q a) (-v).grad) := htriangle
    _ = 2 * localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) h +
        2 * localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v := by
      rw [hneg,
        ← localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
          (Set.Subset.rfl) h,
        ← localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
          (Set.Subset.rfl) v]

/-- One arbitrary-radius half-step obtained from the affine-external active
cells.  The parent comparison energy occurs only in the explicit fine-datum
coefficient; the low-frequency budget contains the preserved physical
difference supplied by the caller. -/
theorem exists_boundaryCrossScale_halfStep_of_affineExternalCells
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE Ad Ag : ℝ} {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (h : H1Function (openCubeSet Q)) (center : Vec d)
        {rhoInner rhoOuter : ℝ},
        (1 / 3 : ℝ) ≤ rhoInner → rhoInner < rhoOuter → rhoOuter < 1 →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K →
        0 ≤ BE → 0 ≤ Ad → 0 ≤ Ag →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g₀ x) →
        MemLp (fun y ↦ u.toH1.toFun y - h.toFun y) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g₀ x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (openCubeSet Q) u.toH1 g₀ →
        MemVectorL2 (openCubeSet Q) g₀ →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (coarseCaccioppoliLocalOpenCube Q center 1)
          (fun y ↦ u.toH1.toFun y - h.toFun y) →
        (let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) h.grad)
          ∀ k : ℕ, descendantsAverage Q (k + 1) Eh ≤ BE) →
        volumeAverage (openCubeSet Q)
            (boundaryCoerciveDatumDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
              (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤ Ad →
        volumeAverage (openCubeSet Q)
            (boundaryCoerciveForceDensity
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
              (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g₀) ≤ Ag →
        boundaryCrossScaleEnergyProfile Q Q center rhoInner (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (u.toH1.grad x)) ≤
          (1 / 2 : ℝ) *
              boundaryCrossScaleEnergyProfile Q Q center rhoOuter (fun x ↦
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                  vecNormSq (u.toH1.grad x)) +
            (5 / 2 : ℝ) * Ad +
            (boundaryCommonGapPowerBudget Q s sigma K C 0
                (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) +
              (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE) *
                Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) +
            (5 / 2 : ℝ) * Ag := by
  obtain ⟨C, hC, hcells⟩ := exists_boundaryCanonicalAdaptiveLocalCells_affineExternal d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE Ad Ag g₀ u h center rhoInner rhoOuter
    hinner hlt houter hs hs4 hsigma hK hBE hAd hAg hupper hlower hreg hu hFL2
    hweak hg hzero hEh hdatum hforce
  obtain ⟨k, hchoice⟩ :=
    exists_coarseCaccioppoliTriadicGapScaleChoice hinner hlt houter.le
  obtain ⟨remainder, hrem, hactive, hremAvg⟩ :=
    hcells M L omega u h center hinner hlt houter.le hchoice hs hs4 hsigma hK
      hBE hupper hlower hreg hu hFL2 (hEh k)
  have hrho : 0 < rhoInner := lt_of_lt_of_le (by norm_num) hinner
  have heta : ContDiff ℝ (⊤ : ℕ∞)
      (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
        (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) :=
    coarseCaccioppoliLocalCanonicalFun_smooth Q center hrho
      (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hetaCompact : HasCompactSupport
      (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
        (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) :=
    coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hrho
      (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hpairOpen := integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
    M L omega u.toH1 h hg heta hetaCompact
  have hpairCube :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hpairOpen
  have henergyOpen := integrableOn_aCutoff_energy M L omega Q u.toH1
  have henergyCube :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr henergyOpen
  have hpairSum :=
    volumeAverage_boundaryCorrectedFluxCutoffPairing_le_outerProfile_of_triadicGapChoice
      M L omega Q Q center k u.toH1 h g₀ remainder hrho hchoice (le_refl _)
        hpairCube henergyCube hrem hactive
  have hpair : |volumeAverage (openCubeSet Q)
      (boundaryCorrectedFluxCutoffPairingDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
        (fun y ↦ u.toH1.toFun y - h.toFun y) u.toH1.grad g₀)| ≤
      (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
        (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (u.toH1.grad x)) +
        (boundaryCommonGapPowerBudget Q s sigma K C 0
            (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) +
          (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE) *
            Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) :=
    hpairSum.trans (add_le_add_right hremAvg _)
  exact boundaryCrossScale_bufferedHalfAbsorbable_of_correctedFluxPairing
    M L omega hweak hg hzero hrho hlt houter hdatum hforce hpair



theorem exists_three_boundaryCrossScale_halfSteps_of_localizedCells
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE : ℝ} {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (h : H1Function (openCubeSet Q)) (center : Vec d)
        {rho₀ rho₁ rho₂ rho₃ : ℝ} (Ad Ag : ℝ → ℝ → ℝ),
        (1 / 3 : ℝ) ≤ rho₀ → rho₀ < rho₁ → rho₁ < rho₂ →
        rho₂ < rho₃ → rho₃ < 1 →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K → 0 ≤ BE →
        (∀ a b, 0 ≤ Ad a b) → (∀ a b, 0 ≤ Ag a b) →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g₀ x) →
        MemLp (fun y ↦ u.toH1.toFun y - h.toFun y) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g₀ x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (openCubeSet Q) u.toH1 g₀ →
        MemVectorL2 (openCubeSet Q) g₀ →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (coarseCaccioppoliLocalOpenCube Q center 1)
          (fun y ↦ u.toH1.toFun y - h.toFun y) →
        (let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) h.grad)
          ∀ k : ℕ, descendantsAverage Q (k + 1) Eh ≤ BE) →
        (∀ a b, (1 / 3 : ℝ) ≤ a → a < b → b < 1 →
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveDatumDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center a
                  (coarseCaccioppoliBufferedCutoffRadius a b)) h.grad) ≤ Ad a b) →
        (∀ a b, (1 / 3 : ℝ) ≤ a → a < b → b < 1 →
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveForceDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center a
                  (coarseCaccioppoliBufferedCutoffRadius a b)) g₀) ≤ Ag a b) →
        let B : ℝ → ℝ → ℝ := fun a b ↦
          (5 / 2 : ℝ) * Ad a b +
          (boundaryCommonGapPowerBudget Q s sigma K C 0
              (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) +
            (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE) *
              Real.rpow (b - a) (-8 : ℝ) +
          (5 / 2 : ℝ) * Ag a b
        (boundaryCrossScaleEnergyProfile Q Q center rho₀ (fun x ↦
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (u.toH1.grad x)) ≤
            (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rho₁
              (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (u.toH1.grad x)) + B rho₀ rho₁) ∧
        (boundaryCrossScaleEnergyProfile Q Q center rho₁ (fun x ↦
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (u.toH1.grad x)) ≤
            (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rho₂
              (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (u.toH1.grad x)) + B rho₁ rho₂) ∧
        boundaryCrossScaleEnergyProfile Q Q center rho₂ (fun x ↦
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (u.toH1.grad x)) ≤
            (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rho₃
              (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (u.toH1.grad x)) + B rho₂ rho₃ := by
  obtain ⟨C, hC, hhalf⟩ := exists_boundaryCrossScale_halfStep_of_affineExternalCells d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE g₀ u h center rho₀ rho₁ rho₂ rho₃
    Ad Ag hthird h01 h12 h23 h3 hs hs4 hsigma hK hBE hAd hAg hupper hlower
    hreg hu hFL2 hweak hg hzero hEh hdatum hforce
  dsimp only
  have h1lt : rho₁ < 1 := lt_trans h12 (lt_trans h23 h3)
  have h2lt : rho₂ < 1 := lt_trans h23 h3
  have hthird1 : (1 / 3 : ℝ) ≤ rho₁ := hthird.trans h01.le
  have hthird2 : (1 / 3 : ℝ) ≤ rho₂ := hthird1.trans h12.le
  have h₀ := hhalf M L omega u h center hthird h01 h1lt hs hs4 hsigma hK
    hBE (hAd _ _) (hAg _ _) hupper hlower hreg hu hFL2 hweak hg hzero hEh
      (hdatum rho₀ rho₁ hthird h01 h1lt)
      (hforce rho₀ rho₁ hthird h01 h1lt)
  have h₁ := hhalf M L omega u h center hthird1 h12 h2lt hs hs4 hsigma hK
    hBE (hAd _ _) (hAg _ _) hupper hlower hreg hu hFL2 hweak hg hzero hEh
      (hdatum rho₁ rho₂ hthird1 h12 h2lt)
      (hforce rho₁ rho₂ hthird1 h12 h2lt)
  have h₂ := hhalf M L omega u h center hthird2 h23 h3 hs hs4 hsigma hK
    hBE (hAd _ _) (hAg _ _) hupper hlower hreg hu hFL2 hweak hg hzero hEh
      (hdatum rho₂ rho₃ hthird2 h23 h3)
      (hforce rho₂ rho₃ hthird2 h23 h3)
  constructor
  · linarith only [h₀]
  constructor
  · linarith only [h₁]
  · linarith only [h₂]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
