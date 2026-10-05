module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCombinedSignedActiveCell
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCrossScaleSummation

@[expose] public section

/-!
# Finite-height aggregation of the combined signed pairing

The residual and affine-lift fluxes stay combined through the finite
descendant sum.  Their three energy prices are represented by one
nonnegative density, so the usual support-buffer argument localizes all of
them to the same outer radius without a triangle inequality on the pairing.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Support-buffer summation for a local quarter of an arbitrary nonnegative
energy.  This specialization is convenient when that energy itself is the
fixed linear combination of residual, lift, and datum energies. -/
theorem abs_cubeAverage_le_quarter_combinedEnergyProfile_of_supportBuffer
    (Q R : TriadicCube d) (center : Vec d) (j : ℕ)
    {rhoSupport rhoOuter : ℝ}
    (pair energy : Vec d → ℝ) (remainder : TriadicCube d → ℝ)
    (hpair : IntegrableOn pair (cubeSet Q) volume)
    (henergyNonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy : IntegrableOn energy (cubeSet Q) volume)
    (hbuffer : ∀ S ∈ descendantsAtDepth Q j,
      cubeScaleFactor S ≤
        (rhoOuter - rhoSupport) * (cubeRadius R / 3))
    (hremainder : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ remainder S)
    (hactive : ∀ S ∈ descendantsAtDepth Q j,
      (∃ y ∈ cubeSet S,
        y ∈ coarseCaccioppoliLocalClosedCube R center rhoSupport) →
      |cubeAverage S pair| ≤
        (1 / 4 : ℝ) * cubeAverage S energy + remainder S)
    (hinactive : ∀ S ∈ descendantsAtDepth Q j,
      ¬ (∃ y ∈ cubeSet S,
        y ∈ coarseCaccioppoliLocalClosedCube R center rhoSupport) →
      cubeAverage S pair = 0) :
    |cubeAverage Q pair| ≤
      (1 / 4 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rhoOuter energy +
        descendantsAverage Q j remainder := by
  exact abs_cubeAverage_le_quarter_crossScaleProfile_of_supportBuffer
    Q R center j pair energy remainder hpair henergyNonneg henergy hbuffer
      hremainder hactive hinactive

/-- The finite-height four-budget cap for the combined signed residual/lift
pairing.  The three explicit energy rows remain localized at the common outer
radius, while the nonlinear finite-height remainder has already collapsed to
the weighted parent carrier. -/
theorem exists_abs_combinedSignedPairing_triadicGap
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE : ℝ} {g : Vec d → Vec d}
        (r v hRes : H1Function (openCubeSet Q)) (center : Vec d)
        {rhoInner rhoOuter : ℝ} {k : ℕ},
        IsDivFormWeakSolutionOn
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) r g →
        IsDivFormWeakSolutionOn
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) v
            (fun _ ↦ 0) →
        0 < rhoInner → rhoInner < rhoOuter →
        CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 ≤ K →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g x) →
        MemLp (r - hRes).toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        MemVectorL2 (openCubeSet Q) g →
        (let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad);
          descendantsAverage Q (k + 1) Eh ≤ BE) →
        let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
        let Er : Vec d → ℝ := fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (r.grad x)
        let Ev : Vec d → ℝ := fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)
        let Eh0 : Vec d → ℝ := fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (hRes.grad x)
        let energy : Vec d → ℝ := fun x ↦ Er x + 2 * Ev x + (1 / 2 : ℝ) * Eh0 x
        |volumeAverage (openCubeSet Q)
            (boundaryCorrectedFluxCutoffPairingDensity
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
              (r - hRes).toFun (r + (2 : ℝ) • v).grad g)| ≤
          (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter energy +
            4 * boundaryCommonYoungParentBudgetWeighted Q k rhoInner rhoOuter
              s sigma K C BE (r - hRes).toFun (fun x ↦ -g x) := by
  obtain ⟨C, hC, hcell⟩ := exists_boundaryCombinedSignedActiveCell_commonHeight d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE g r v hRes center rhoInner rhoOuter k
    hweakR hweakV hinner hlt hchoice hs hs4 hsigma hK hupper hlower hreg
    hresL2 hgL2 hgOpen hEhavg
  dsimp only
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
  let pair := boundaryCorrectedFluxCutoffPairingDensity
    (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
    (r - hRes).toFun (r + (2 : ℝ) • v).grad g
  let Er : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (r.grad x)
  let Ev : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (v.grad x)
  let Eh0 : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (hRes.grad x)
  let energy : Vec d → ℝ := fun x ↦ Er x + 2 * Ev x + (1 / 2 : ℝ) * Eh0 x
  let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
    (coefficientEnergyDensity
      (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad)
  let remainder : TriadicCube d → ℝ := fun S ↦
    4 * boundaryCommonYoungRemainder Q k rhoInner rhoOuter
      s sigma K C (r - hRes).toFun (fun x ↦ -g x) Eh S
  have hrho : 0 < rhoInner := hinner
  have hsupport : rhoInner <
      coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter :=
    (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hetaSmooth : ContDiff ℝ (⊤ : ℕ∞) eta :=
    coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hsupport
  have hetaCompact : HasCompactSupport eta :=
    coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner hsupport
  let combinedDatum : H1Function (openCubeSet Q) := (2 : ℝ) • v + hRes
  have hpairOpen := integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
    M L omega (r + (2 : ℝ) • v) combinedDatum
      hgOpen hetaSmooth hetaCompact
  have hpairEq :
      boundaryCorrectedFluxCutoffPairingDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
        (fun y ↦ (r + (2 : ℝ) • v).toFun y - combinedDatum.toFun y)
        (r + (2 : ℝ) • v).grad g = pair := by
    have hw : (fun y ↦ (r + (2 : ℝ) • v).toFun y - combinedDatum.toFun y) =
        (r - hRes).toFun := by
      funext y
      simp only [combinedDatum, H1Function.add_toFun, H1Function.smul_toFun,
        H1Function.sub_toFun]
      ring
    rw [hw]
  have hpairCube : IntegrableOn pair (cubeSet Q) := by
    rw [← hpairEq, integrableOn_cubeSet_iff_integrableOn_openCubeSet]
    exact hpairOpen
  have hrInt : IntegrableOn Er (cubeSet Q) := by
    rw [integrableOn_cubeSet_iff_integrableOn_openCubeSet]
    simpa only [Er] using integrableOn_aCutoff_energy M L omega Q r
  have hvInt : IntegrableOn Ev (cubeSet Q) := by
    rw [integrableOn_cubeSet_iff_integrableOn_openCubeSet]
    simpa only [Ev] using integrableOn_aCutoff_energy M L omega Q v
  have hhInt : IntegrableOn Eh0 (cubeSet Q) := by
    rw [integrableOn_cubeSet_iff_integrableOn_openCubeSet]
    simpa only [Eh0] using integrableOn_aCutoff_energy M L omega Q hRes
  have henergyInt : IntegrableOn energy (cubeSet Q) := by
    dsimp only [energy]
    exact hrInt.add (hvInt.const_mul 2) |>.add (hhInt.const_mul (1 / 2 : ℝ))
  have henergy0 : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    intro x _
    dsimp only [energy, Er, Ev, Eh0]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le
          (vecNormSq_nonneg _))
        (mul_nonneg (by norm_num)
          (mul_nonneg (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le
            (vecNormSq_nonneg _))))
      (mul_nonneg (by norm_num)
        (mul_nonneg (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le
          (vecNormSq_nonneg _)))
  have hbuffer : ∀ S ∈ descendantsAtDepth Q (k + 1),
      cubeScaleFactor S ≤
        (rhoOuter - coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) *
          (cubeRadius Q / 3) := by
    intro S hS
    have hbase :=
      cubeScaleFactor_le_local_buffer_of_mem_descendantsAtDepth_succ_of_triadicGapScaleChoice
        hS hchoice le_rfl
    simpa only using hbase
  have hEh0 : ∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ Eh S := by
    intro S hS
    dsimp only [Eh]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn S
      (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet S (aCutoffFamily M L omega))
  have hrem0 : ∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ remainder S := by
    intro S hS
    dsimp only [remainder]
    exact mul_nonneg (by norm_num)
      (boundaryCommonYoungRemainder_nonneg hinner hlt hs hC.le (hEh0 S hS)
        (forceBesovRegularity_descendant hreg hS))
  have hactive : ∀ S ∈ descendantsAtDepth Q (k + 1),
      (∃ y ∈ cubeSet S,
        y ∈ coarseCaccioppoliLocalClosedCube Q center
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) →
      |cubeAverage S pair| ≤ (1 / 4 : ℝ) * cubeAverage S energy + remainder S := by
    intro S hS _hmeet
    let hSQ : openCubeSet S ⊆ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hS
    let rS := r.restrictToOpenSubcube hS
    let vS := v.restrictToOpenSubcube hS
    let hSres := hRes.restrictToOpenSubcube hS
    have hweakRS := isDivFormWeakSolutionOn_restrict
      (isOpen_openCubeSet Q) (isOpen_openCubeSet S) hSQ hweakR
    have hweakVS := isDivFormWeakSolutionOn_restrict
      (isOpen_openCubeSet Q) (isOpen_openCubeSet S) hSQ hweakV
    have hlocal := hcell M L omega rS vS hSres hweakRS hweakVS center hS
      hinner hlt hchoice hs hs4 hsigma hK hupper hlower
      (forceBesovRegularity_descendant hreg hS)
    have hrEq : cubeAverage S
        (coefficientEnergyDensity
          (publicCoeffField S (aCutoffFamily M L omega)) r.grad) =
        cubeAverage S Er := by
      apply cubeAverage_eq_of_ae_eq_on_cubeSet
      filter_upwards [publicCoeffField_ae_eq_cubeSet S
        (aCutoffFamily M L omega)] with x hx
      simp only [Er, coefficientEnergyDensity, hx]
      simp [aCutoffFamily, aCutoffTriadicData,
        ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
        ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
        Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
        vecDot_smul_right, vecNormSq]
    have hvEq : cubeAverage S
        (coefficientEnergyDensity
          (publicCoeffField S (aCutoffFamily M L omega)) v.grad) =
        cubeAverage S Ev := by
      apply cubeAverage_eq_of_ae_eq_on_cubeSet
      filter_upwards [publicCoeffField_ae_eq_cubeSet S
        (aCutoffFamily M L omega)] with x hx
      simp only [Ev, coefficientEnergyDensity, hx]
      simp [aCutoffFamily, aCutoffTriadicData,
        ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
        ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
        Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
        vecDot_smul_right, vecNormSq]
    have hhEq : cubeAverage S
        (coefficientEnergyDensity
          (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad) =
        cubeAverage S Eh0 := by
      apply cubeAverage_eq_of_ae_eq_on_cubeSet
      filter_upwards [publicCoeffField_ae_eq_cubeSet S
        (aCutoffFamily M L omega)] with x hx
      simp only [Eh0, coefficientEnergyDensity, hx]
      simp [aCutoffFamily, aCutoffTriadicData,
        ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
        ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
        Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
        vecDot_smul_right, vecNormSq]
    have henergyEq : cubeAverage S energy =
        cubeAverage S Er + 2 * cubeAverage S Ev + (1 / 2 : ℝ) * cubeAverage S Eh0 := by
      have hsub := cubeSet_subset_of_mem_descendantsAtDepth hS
      have hrS := hrInt.mono_set hsub
      have hvS := hvInt.mono_set hsub
      have hhS := hhInt.mono_set hsub
      have hv2S : IntegrableOn (fun x ↦ 2 * Ev x) (cubeSet S) := hvS.const_mul 2
      have hh2S : IntegrableOn (fun x ↦ (1 / 2 : ℝ) * Eh0 x) (cubeSet S) :=
        hhS.const_mul (1 / 2 : ℝ)
      have hfirst := cubeAverage_add_of_integrableOn S Er (fun x ↦ 2 * Ev x)
        hrS hv2S
      have hsecond := cubeAverage_add_of_integrableOn S
        (fun x ↦ Er x + 2 * Ev x) (fun x ↦ (1 / 2 : ℝ) * Eh0 x)
        (hrS.add hv2S) hh2S
      dsimp only [energy]
      rw [hsecond, hfirst, cubeAverage_const_mul, cubeAverage_const_mul]
    have hlocal' := hlocal
    simp only [rS, vS, hSres, H1Function.restrictToOpenSubcube_grad] at hlocal'
    change |cubeAverage S
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
          (r - hRes).toFun (r + (2 : ℝ) • v).grad g)| ≤
      (1 / 4 : ℝ) * cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) r.grad) +
        (1 / 2 : ℝ) * cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) v.grad) +
        (1 / 8 : ℝ) * cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad) +
        4 * boundaryCommonYoungRemainder Q k rhoInner rhoOuter
          s sigma K C (r - hRes).toFun (fun x ↦ -g x) Eh S at hlocal'
    rw [hrEq, hvEq, hhEq] at hlocal'
    rw [henergyEq]
    dsimp only [remainder, Eh]
    linarith only [hlocal']
  have hinactive : ∀ S ∈ descendantsAtDepth Q (k + 1),
      ¬ (∃ y ∈ cubeSet S,
        y ∈ coarseCaccioppoliLocalClosedCube Q center
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) →
      cubeAverage S pair = 0 := by
    intro S _hS hdisjoint
    dsimp only [pair, eta]
    exact cubeAverage_boundaryCorrectedFluxCutoffPairingDensity_eq_zero_of_disjoint
      hinner hsupport hdisjoint
  have hsum := abs_cubeAverage_le_quarter_combinedEnergyProfile_of_supportBuffer
    Q Q center (k + 1) pair energy remainder hpairCube henergy0 henergyInt
      hbuffer hrem0 hactive hinactive
  have hremAvg := descendantsAverage_boundaryCommonYoungRemainder_le_weighted
    (K := K) Q k (r - hRes).toFun (fun x ↦ -g x) Eh
      hinner hlt hs hs4 hsigma hC.le
      hresL2 hreg hgL2 hEh0 (by simpa only [Eh] using hEhavg)
  have hremAvg4 := mul_le_mul_of_nonneg_left hremAvg (by norm_num : (0 : ℝ) ≤ 4)
  have hremEq : descendantsAverage Q (k + 1) remainder =
      4 * descendantsAverage Q (k + 1)
        (boundaryCommonYoungRemainder Q k rhoInner rhoOuter
          s sigma K C (r - hRes).toFun (fun x ↦ -g x) Eh) := by
    dsimp only [remainder]
    exact descendantsAverage_mul_left Q (k + 1) 4 _
  rw [hremEq] at hsum
  rw [volumeAverage_openCubeSet_eq_cubeAverage]
  dsimp only [pair, energy, Er, Ev, Eh0, eta] at hsum ⊢
  linarith only [hsum, hremAvg4]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
