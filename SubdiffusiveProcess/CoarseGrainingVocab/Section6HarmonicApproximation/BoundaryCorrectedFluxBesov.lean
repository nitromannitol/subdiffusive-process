module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCorrectedFluxRecurrence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDifferencePrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryH1PositiveBesov
public import Homogenization.Book.Ch03.Theorems.DualityPositivePairing
public import Homogenization.Book.Ch03.Theorems.WeakFluxRHS

@[expose] public section

/-!
# The corrected boundary flux in the public Besov carrier

The manuscript weak equation has the opposite forcing sign from Chapter 3.
Consequently the vector field paired with the cutoff product is the Chapter-3
flux minus its forcing.  This file gives that corrected field its missing
`q = 2` negative-Besov estimate.  It is the nonzero-boundary-datum counterpart
of the flux input used by the library's zero-trace Caccioppoli argument.

The decomposition uses the weak-flux/cutoff-product split; the actual
weak-flux bound is the public Chapter-3 `weakFluxRHSTheory`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The residual-solenoidal (or corrected) flux in Chapter-3's forcing sign
convention.  For the manuscript equation with source `g₀`, instantiate this
with Chapter-3 forcing `-g₀`; the value is then `a grad u + g₀`. -/
noncomputable def forcedSolutionCorrectedFluxField
    (Q : TriadicCube d) (a : CoeffFamily d) (g : Vec d → Vec d)
    (u : ForcedCubeSolution Q a g) : Vec d → Vec d :=
  fun x ↦ matVecMul (publicCoeffField Q a x) (forcedSolutionGradientField u x) - g x

omit [NeZero d] in
private theorem memVectorL2_openCubeSet_of_cubeSet {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (cubeSet Q) F) :
    MemVectorL2 (openCubeSet Q) F := by
  rw [MemVectorL2, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at hF
  exact hF

/-- The corrected flux is locally square integrable. -/
theorem memVectorL2_forcedSolutionCorrectedFluxField
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ} {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) (hg : ForceBesovRegularity Q s g) :
    MemVectorL2 (cubeSet Q) (forcedSolutionCorrectedFluxField Q a g u) := by
  have hQ : Q ∈ descendantsAtDepth Q 0 := by simp [descendantsAtDepth_zero]
  exact (forcedSolutionPublicFlux_memVectorL2_descendant_cubeSet u hQ).sub
    (memVectorL2_cubeSet_of_forceBesovRegularity hg)

/-- The corrected flux is weakly solenoidal.  This is the exact reason that
the constant mode of a nonzero boundary datum does not enter the cutoff
pairing. -/
theorem isSolenoidalOn_forcedSolutionCorrectedFluxField
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ} {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) (hg : ForceBesovRegularity Q s g) :
    IsSolenoidalOn (openCubeSet Q)
      (forcedSolutionCorrectedFluxField Q a g u) := by
  intro phi
  let F : Vec d → Vec d := fun x ↦
    matVecMul (publicCoeffField Q a x) (forcedSolutionGradientField u x)
  have hQ : Q ∈ descendantsAtDepth Q 0 := by simp [descendantsAtDepth_zero]
  have hFcube : MemVectorL2 (cubeSet Q) F := by
    simpa [F] using forcedSolutionPublicFlux_memVectorL2_descendant_cubeSet u hQ
  have hF : MemVectorL2 (openCubeSet Q) F :=
    memVectorL2_openCubeSet_of_cubeSet hFcube
  have hgcube : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_forceBesovRegularity hg
  have hgopen : MemVectorL2 (openCubeSet Q) g :=
    memVectorL2_openCubeSet_of_cubeSet hgcube
  have hphi : MemVectorL2 (openCubeSet Q) phi.toH1Function.grad :=
    phi.toH1Function.grad_memVectorL2
  have hFint : IntegrableOn
      (fun x ↦ vecDot (F x) (phi.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hF hphi
  have hgint : IntegrableOn
      (fun x ↦ vecDot (g x) (phi.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hgopen hphi
  have hcoeff :
      ∫ x in openCubeSet Q,
          vecDot (F x) (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x)
            (u.toH1.grad x)) (phi.toH1Function.grad x) ∂volume := by
    apply integral_congr_ae
    filter_upwards [publicCoeffField_ae_eq Q a] with x hx
    simp [F, forcedSolutionGradientField, hx]
  have hweak := u.weakSolution phi
  unfold forcedSolutionCorrectedFluxField
  change ∫ x in openCubeSet Q,
      vecDot (F x - g x) (phi.toH1Function.grad x) ∂volume = 0
  rw [show (fun x ↦ vecDot (F x - g x) (phi.toH1Function.grad x)) =
      fun x ↦ vecDot (F x) (phi.toH1Function.grad x) -
        vecDot (g x) (phi.toH1Function.grad x) by
    funext x
    simp [vecDot, Finset.sum_sub_distrib, sub_mul]]
  have hweak' :
      ∫ x in openCubeSet Q,
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x)
            (u.toH1.grad x)) (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
    simpa [Ch02.cubeDomain_coe] using hweak
  rw [integral_sub hFint hgint, hcoeff, hweak', sub_self]

/-- A constant scalar mode pairs to zero with the corrected flux against the
gradient of a compactly supported smooth cutoff. -/
theorem cubeAverage_correctedFlux_const_smul_cutoffGradient_eq_zero
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ} {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) (hg : ForceBesovRegularity Q s g)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaSupport : tsupport eta ⊆ openCubeSet Q)
    (c : ℝ) :
    cubeAverage Q (fun x ↦
      vecDot (forcedSolutionCorrectedFluxField Q a g u x)
        (c • scalarCutoffGradientField eta x)) = 0 := by
  have hsol := isSolenoidalOn_forcedSolutionCorrectedFluxField u hg
  have htest := hsol.test_of_contDiff (isOpen_openCubeSet Q) heta hetaCompact hetaSupport
  have htest' :
      ∫ x in openCubeSet Q,
        vecDot (forcedSolutionCorrectedFluxField Q a g u x)
          (scalarCutoffGradientField eta x) ∂volume = 0 := by
    simpa +instances [scalarCutoffGradientField, euclideanCoordDeriv] using! htest
  rw [← volumeAverage_openCubeSet_eq_cubeAverage_local]
  unfold volumeAverage
  rw [show (fun x ↦
      vecDot (forcedSolutionCorrectedFluxField Q a g u x)
        (c • scalarCutoffGradientField eta x)) =
      fun x ↦ c * vecDot (forcedSolutionCorrectedFluxField Q a g u x)
        (scalarCutoffGradientField eta x) by
    funext x
    rw [vecDot_smul_right]]
  rw [integral_const_mul, htest']
  ring

/-- Centering the scalar factor does not change its corrected-flux cutoff
pairing.  This is the constant-mode removal needed before invoking the
full-vector Poincaré cutoff-product estimate. -/
theorem cubeAverage_correctedFlux_scalar_smul_cutoffGradient_eq_centered
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ} {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) (hg : ForceBesovRegularity Q s g)
    (w : Vec d → ℝ) {eta : Vec d → ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaSupport : tsupport eta ⊆ openCubeSet Q)
    (hmain : Integrable (fun x ↦
      vecDot (forcedSolutionCorrectedFluxField Q a g u x)
        (w x • scalarCutoffGradientField eta x)) (normalizedCubeMeasure Q))
    (hconst : Integrable (fun x ↦
      vecDot (forcedSolutionCorrectedFluxField Q a g u x)
        ((cubeAverage Q w) • scalarCutoffGradientField eta x))
      (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x ↦
        vecDot (forcedSolutionCorrectedFluxField Q a g u x)
          (w x • scalarCutoffGradientField eta x)) =
      cubeAverage Q (fun x ↦
        vecDot (forcedSolutionCorrectedFluxField Q a g u x)
          ((w x - cubeAverage Q w) • scalarCutoffGradientField eta x)) := by
  have hzero := cubeAverage_correctedFlux_const_smul_cutoffGradient_eq_zero
    u hg heta hetaCompact hetaSupport (cubeAverage Q w)
  have hsplit : (fun x ↦
      vecDot (forcedSolutionCorrectedFluxField Q a g u x)
        (w x • scalarCutoffGradientField eta x)) =
      fun x ↦
        vecDot (forcedSolutionCorrectedFluxField Q a g u x)
          ((w x - cubeAverage Q w) • scalarCutoffGradientField eta x) +
        vecDot (forcedSolutionCorrectedFluxField Q a g u x)
          ((cubeAverage Q w) • scalarCutoffGradientField eta x) := by
    funext x
    rw [← vecDot_add_right]
    congr 1
    module
  have hcenter : Integrable (fun x ↦
      vecDot (forcedSolutionCorrectedFluxField Q a g u x)
        ((w x - cubeAverage Q w) • scalarCutoffGradientField eta x))
      (normalizedCubeMeasure Q) := by
    have heq : (fun x ↦
        vecDot (forcedSolutionCorrectedFluxField Q a g u x)
          ((w x - cubeAverage Q w) • scalarCutoffGradientField eta x)) =
        (fun x ↦
          vecDot (forcedSolutionCorrectedFluxField Q a g u x)
            (w x • scalarCutoffGradientField eta x)) -
        (fun x ↦
          vecDot (forcedSolutionCorrectedFluxField Q a g u x)
            ((cubeAverage Q w) • scalarCutoffGradientField eta x)) := by
      funext x
      unfold vecDot
      simp only [Pi.sub_apply]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact hmain.sub hconst
  rw [hsplit, cubeAverage_eq_integral_normalizedCubeMeasure,
    integral_add hcenter hconst, ← cubeAverage_eq_integral_normalizedCubeMeasure,
    ← cubeAverage_eq_integral_normalizedCubeMeasure, hzero, add_zero]

/-- Forget the boundary datum while retaining a Dirichlet forced solution's
weak equation. -/
def forcedCubeSolutionOfDirichlet {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g) :
    ForcedCubeSolution Q a g where
  toH1 := v.toH1
  weakSolution := v.weakSolution

omit [NeZero d] in
/-- In the scalar GMC family and with the manuscript/library sign conversion,
the public corrected flux pairing is exactly the localized pairing density
from the direct weak test. -/
theorem cubeAverage_correctedFluxPairing_eq_volumeAverage_boundaryDensity
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (g₀ : Vec d → Vec d)
    (v : DirichletForcedCubeSolution (Q := Q)
      (aCutoffFamily M L omega) (fun x => -g₀ x))
    (w eta : Vec d → ℝ) :
    cubeAverage Q (fun x =>
        vecDot
          (forcedSolutionCorrectedFluxField Q (aCutoffFamily M L omega)
            (fun y => -g₀ y) (forcedCubeSolutionOfDirichlet v) x)
          (w x • scalarCutoffGradientField (fun y => eta y ^ 2) x)) =
      volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta w v.toH1.grad g₀) := by
  rw [volumeAverage_openCubeSet_eq_cubeAverage_local]
  apply cubeAverage_eq_of_ae_eq_on_cubeSet
  filter_upwards [publicCoeffField_ae_eq_cubeSet Q (aCutoffFamily M L omega)]
    with x hx
  unfold forcedSolutionCorrectedFluxField boundaryCorrectedFluxCutoffPairingDensity
    boundaryCorrectedFlux
  change vecDot
      (matVecMul (publicCoeffField Q (aCutoffFamily M L omega) x) (v.toH1.grad x) -
        -g₀ x)
      (w x • scalarCutoffGradientField (fun y => eta y ^ 2) x) = _
  rw [hx]
  simp only [aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField, matVecMul_scalarMatrix,
    sub_neg_eq_add]

omit [NeZero d] in
/-- The forcing's negative `q = 2` Besov norm is controlled by its normalized
Euclidean `L²` norm. -/
theorem scaleNormalizedNegativeBesovVectorNorm_forcing_le_l2
    {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hs : 0 < s) (hg : ForceBesovRegularity Q s g) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2) g ≤
      boundaryNegativeToL2Factor (2 * s) * boundaryNormalizedEuclideanL2 Q g := by
  rw [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
  have hgOpen : MemVectorL2 (openCubeSet Q) g :=
    memVectorL2_openCubeSet_of_cubeSet
      (memVectorL2_cubeSet_of_forceBesovRegularity hg)
  simpa [show 2 * s / 2 = s by ring] using
    cubeBesovNegativeVectorSeminormTwo_le_normalizedEuclideanL2
      (Q := Q) (s := 2 * s) (by positivity) hgOpen

/-- Public weak-flux estimate for the corrected flux.  This is the precise
Besov input needed by the nonzero-datum cutoff pairing; unlike a pointwise
coefficient cap, its coefficient dependence is entirely through the
multiscale quantities inside `weakFluxWithRHSRHS`. -/
theorem exists_correctedFlux_negativeBesov_le_weakFlux_add_forcingL2
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g),
        0 < s → s < 1 → ForceBesovRegularity Q s g →
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2)
              (forcedSolutionCorrectedFluxField Q a g u) ≤
            Real.sqrt 2 *
              (weakFluxWithRHSRHS C Q a s g u +
                boundaryNegativeToL2Factor (2 * s) *
                  boundaryNormalizedEuclideanL2 Q g) := by
  obtain ⟨C, hC, hweak⟩ := (weakFluxRHSTheory (d := d)).exists_constant
  refine ⟨C, hC, ?_⟩
  intro Q a s g u hs hs1 hg
  let F : Vec d → Vec d := fun x ↦
    matVecMul (publicCoeffField Q a x) (forcedSolutionGradientField u x)
  have hQ : Q ∈ descendantsAtDepth Q 0 := by simp [descendantsAtDepth_zero]
  have hF : MemVectorL2 (cubeSet Q) F := by
    simpa [F] using forcedSolutionPublicFlux_memVectorL2_descendant_cubeSet u hQ
  have hgL2 : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_forceBesovRegularity hg
  have hFBdd : BddAbove (Set.range fun N : ℕ ↦
      cubeBesovNegativeVectorPartialSeminormTwo Q s N F) := by
    exact cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs F
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hF)
  have hgBdd : BddAbove (Set.range fun N : ℕ ↦
      cubeBesovNegativeVectorPartialSeminormTwo Q s N g) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs g
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hgL2)
  have hsub := cubeBesovNegativeVectorSeminormTwo_sub_le_sqrtTwo_mul_add_of_bddAbove
    Q s F g hF hgL2 hFBdd hgBdd
  have hflux : cubeBesovNegativeVectorSeminormTwo Q s F ≤
      weakFluxWithRHSRHS C Q a s g u := by
    have hbase := hweak u hs hs1 hg
    have heq :=
      scaleNormalizedNegativeBesovVectorNorm_forcedSolutionFluxField_finite_two_eq_cubeBesovNegativeVectorSeminormTwo_publicCoeffField
        Q a s u
    rw [heq] at hbase
    simpa [F] using hbase
  have hgneg := scaleNormalizedNegativeBesovVectorNorm_forcing_le_l2 hs hg
  rw [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
    at hgneg ⊢
  have hadd := add_le_add hflux hgneg
  exact hsub.trans (mul_le_mul_of_nonneg_left hadd (Real.sqrt_nonneg _))



theorem exists_abs_correctedFlux_pairing_le_weakFlux_mul_positiveBesov
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        {g H : Vec d → Vec d} (u : ForcedCubeSolution Q a g) {B : ℝ},
        0 < s → s < 1 → ForceBesovRegularity Q s g →
        ForceBesovRegularity Q s H → 0 ≤ B →
        scaleNormalizedPositiveBesovVectorNormTwo Q s H ≤ B →
          |cubeAverage Q (fun x =>
            vecDot (forcedSolutionCorrectedFluxField Q a g u x) (H x))| ≤
            C * (weakFluxWithRHSRHS C Q a s g u +
                boundaryNegativeToL2Factor (2 * s) *
                  boundaryNormalizedEuclideanL2 Q g) * B := by
  obtain ⟨Cw, hCw, hcorr⟩ :=
    exists_correctedFlux_negativeBesov_le_weakFlux_add_forcingL2 d
  let Cdual : ℝ := 1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)
  let C : ℝ := max Cw (Real.sqrt 2 * Cdual)
  have hC : 0 < C := hCw.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro Q a s g H u B hs hs1 hg hH hB hHnorm
  let F : Vec d → Vec d := forcedSolutionCorrectedFluxField Q a g u
  let R : ℝ := Real.sqrt 2 *
    (weakFluxWithRHSRHS C Q a s g u +
      boundaryNegativeToL2Factor (2 * s) * boundaryNormalizedEuclideanL2 Q g)
  have hmono : weakFluxWithRHSRHS Cw Q a s g u ≤
      weakFluxWithRHSRHS C Q a s g u := by
    unfold weakFluxWithRHSRHS
    have hCwC : Cw ≤ C := le_max_left _ _
    have hsInv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    have hupper : 0 ≤ poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) := by
      unfold poincareUpperEllipticityFactor
      exact Real.rpow_nonneg (Ch02.LambdaSq_nonneg Q a (by positivity) (by norm_num)) _
    have hlower : 0 ≤ poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) := by
      unfold poincareLowerEllipticityFactor
      exact Real.rpow_nonneg (Ch02.lambdaSq_nonneg Q a (by positivity) (by norm_num)) _
    have hE : 0 ≤ forcedSolutionEnergyNorm Q a u := by
      unfold forcedSolutionEnergyNorm
      exact Real.sqrt_nonneg _
    have hG : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q s g :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hg
    have hsPow : 0 ≤ Real.rpow s (-(5 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
    have hfirst : Cw * s⁻¹ * poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
          forcedSolutionEnergyNorm Q a u ≤
        C * s⁻¹ * poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
          forcedSolutionEnergyNorm Q a u := by
      calc
        _ = Cw * (s⁻¹ * poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
            forcedSolutionEnergyNorm Q a u) := by ring
        _ ≤ C * (s⁻¹ * poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
            forcedSolutionEnergyNorm Q a u) :=
          mul_le_mul_of_nonneg_right hCwC
            (mul_nonneg (mul_nonneg hsInv hupper) hE)
        _ = _ := by ring
    have hsecond : Cw * Real.rpow s (-(5 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
          poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q s g ≤
        C * Real.rpow s (-(5 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
          poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
      calc
        _ = Cw * (Real.rpow s (-(5 / 2 : ℝ)) *
            poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
            poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) := by ring
        _ ≤ C * (Real.rpow s (-(5 / 2 : ℝ)) *
            poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
            poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) :=
          mul_le_mul_of_nonneg_right hCwC
            (mul_nonneg (mul_nonneg (mul_nonneg hsPow hupper) hlower) hG)
        _ = _ := by ring
    exact add_le_add hfirst hsecond
  have hcorrCw := hcorr u hs hs1 hg
  have hcorrC : scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2) F ≤ R := by
    dsimp only [F, R]
    exact hcorrCw.trans
      (mul_le_mul_of_nonneg_left
        (add_le_add hmono le_rfl) (Real.sqrt_nonneg _))
  have hFL2 : MemVectorL2 (cubeSet Q) F := by
    simpa [F] using memVectorL2_forcedSolutionCorrectedFluxField u hg
  have hFBdd : BddAbove (Set.range fun N : ℕ ↦
      cubeBesovNegativeVectorPartialSeminormTwo Q s N F) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs F
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hFL2)
  have hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N F ≤ R := by
    intro N
    rw [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
      at hcorrC
    exact (cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
      Q s F hFBdd N).trans hcorrC
  have hR : 0 ≤ R := by
    have hsemi : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q s F :=
      cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove Q s F hFBdd
    rw [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
      at hcorrC
    exact hsemi.trans hcorrC
  have hpair :=
    abs_cubeAverage_vecDot_le_public_negative_positive_besov_duality_of_partial_flux_bound
      (Q := Q) (s := s) (Bflux := R) (F := F) (H := H)
      hs hs1.le (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hFL2)
      hH hR hneg
  have hCdual : 0 ≤ Cdual := by
    dsimp [Cdual]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hHnorm
    (mul_nonneg hCdual hR)
  have hcoeff : Real.sqrt 2 * Cdual ≤ C := le_max_right _ _
  have hsum : 0 ≤ weakFluxWithRHSRHS C Q a s g u +
      boundaryNegativeToL2Factor (2 * s) * boundaryNormalizedEuclideanL2 Q g := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    dsimp only [R] at hR
    rw [mul_comm] at hR
    exact nonneg_of_mul_nonneg_left hR hsqrt
  have hrest : 0 ≤
      (weakFluxWithRHSRHS C Q a s g u +
        boundaryNegativeToL2Factor (2 * s) * boundaryNormalizedEuclideanL2 Q g) * B :=
    mul_nonneg hsum hB
  have hfinal : |cubeAverage Q (fun x => vecDot (F x) (H x))| ≤
      C * (weakFluxWithRHSRHS C Q a s g u +
          boundaryNegativeToL2Factor (2 * s) * boundaryNormalizedEuclideanL2 Q g) * B := by
    calc
    |cubeAverage Q (fun x => vecDot (F x) (H x))| ≤
        Cdual * R * scaleNormalizedPositiveBesovVectorNormTwo Q s H := by
          simpa [Cdual] using hpair
    _ ≤ Cdual * R * B := hscaled
    _ = (Real.sqrt 2 * Cdual) *
          (weakFluxWithRHSRHS C Q a s g u +
            boundaryNegativeToL2Factor (2 * s) * boundaryNormalizedEuclideanL2 Q g) * B := by
          dsimp [R]
          ring
    _ ≤ C *
          (weakFluxWithRHSRHS C Q a s g u +
            boundaryNegativeToL2Factor (2 * s) * boundaryNormalizedEuclideanL2 Q g) * B := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff hrest
  simpa only [F] using hfinal

/-- The centered product of an `H¹` scalar with a smooth cutoff gradient has
the exact positive regularity required by the corrected-flux pairing.  Unlike
the older componentwise route, this estimate is valid for arbitrary `H¹`
functions and therefore retains nonzero boundary data. -/
theorem centeredH1CutoffProduct_positiveBesovBudget
    {Q : TriadicCube d} {s : ℝ} (u : H1Function (openCubeSet Q))
    (xi : Vec d → Vec d) {B : ℝ}
    (hB : 0 ≤ B)
    (hxiLp : MemLp xi ∞ (normalizedCubeMeasure Q))
    (hxi : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => xi x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => xi x i) z‖ ≤ B)
    (hs : s < 1) :
    let v : Vec d → ℝ := cubeFluctuation Q u.toFun
    let H : Vec d → Vec d := fun x => v x • xi x
    let Gs : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹)
    let X : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) v
    let Y : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x))
    ForceBesovRegularity Q s H ∧
      scaleNormalizedPositiveBesovVectorNormTwo Q s H ≤
        (d : ℝ) * cubeLpNorm Q ∞ xi * X +
          2 * (cubeScaleFactor Q * B * (Gs * X) +
            cubeLpNorm Q ∞ xi *
              (cubeScaleFactor Q * Gs * (cubeBesovW12EmbeddingConstant d * Y))) := by
  dsimp only
  let v : Vec d → ℝ := cubeFluctuation Q u.toFun
  let H : Vec d → Vec d := fun x => v x • xi x
  let Gs : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹)
  let X : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) v
  let Y : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x))
  have hu : MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hv : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (memLp_const (cubeAverage Q u.toFun))
  have hH : MemLp H (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
    simpa [H] using! hv.smul (p := (2 : ℝ≥0∞)) (q := ∞) (r := (2 : ℝ≥0∞)) hxiLp
  have hL2 : ∀ N : ℕ,
      cubeL2ScalarPartialSeminormTwo Q (s - 1) N v ≤ Gs * X := by
    intro N
    simpa [v, Gs, X] using
      cubeL2ScalarPartialSeminormTwo_le_geometric_mul_cubeLpNorm_two_of_neg
        Q (s - 1) N v hv (by linarith)
  have hpos : ∀ N : ℕ,
      cubeBesovPositiveScalarPartialSeminormTwo Q s N v ≤
        cubeScaleFactor Q * Gs * (cubeBesovW12EmbeddingConstant d * Y) := by
    intro N
    have hraw := cubeBesovPositiveScalarPartialSeminormTwo_h1_le Q s N u hs
    have hmem : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
        MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
      intro j hj R hR
      exact memLp_on_descendant_of_memLp_generic (E := ℝ) hR hu
    have heq := cubeBesovPositiveScalarPartialSeminormTwo_sub_const
      Q s N u.toFun (cubeAverage Q u.toFun) hmem
    change cubeBesovPositiveScalarPartialSeminormTwo Q s N
        (fun x => u.toFun x - cubeAverage Q u.toFun) ≤ _
    rw [heq]
    simpa only [Gs, Y] using hraw
  let P : ℝ := 2 * (cubeScaleFactor Q * B * (Gs * X) +
    cubeLpNorm Q ∞ xi *
      (cubeScaleFactor Q * Gs * (cubeBesovW12EmbeddingConstant d * Y)))
  have hpartial : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N H ≤ P := by
    intro N
    have hraw :=
      cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
        Q s N u.toFun xi hB hu hxiLp hxi hderiv
    have hcoeff1 : 0 ≤ cubeScaleFactor Q * B :=
      mul_nonneg (cubeScaleFactor_nonneg Q) hB
    have hcoeff2 : 0 ≤ cubeLpNorm Q ∞ xi := cubeLpNorm_nonneg Q ∞ xi
    have h1 := mul_le_mul_of_nonneg_left (hL2 N) hcoeff1
    have h2 := mul_le_mul_of_nonneg_left (hpos N) hcoeff2
    dsimp only [H, v] at hraw ⊢
    dsimp only [P]
    exact hraw.trans (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num))
  have hreg : ForceBesovRegularity Q s H := by
    refine ⟨hH, ?_⟩
    exact ⟨P, by rintro _ ⟨N, rfl⟩; exact hpartial N⟩
  have hsemi : cubeBesovPositiveVectorSeminormTwo Q s H ≤ P :=
    cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q s H hpartial
  have havgNorm : ‖cubeAverageVec Q H‖ ≤ cubeLpNorm Q ∞ xi * X := by
    simpa [H, X] using
      norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two
        Q v xi hv hxiLp
  have havgEuclidean : Real.sqrt (vecNormSq (cubeAverageVec Q H)) ≤
      (d : ℝ) * cubeLpNorm Q ∞ xi * X := by
    calc
      Real.sqrt (vecNormSq (cubeAverageVec Q H)) =
          euclideanNorm (cubeAverageVec Q H) := rfl
      _ ≤ (d : ℝ) * ‖cubeAverageVec Q H‖ :=
        euclideanNorm_le_dimension_mul_norm _
      _ ≤ (d : ℝ) * (cubeLpNorm Q ∞ xi * X) := by
        exact mul_le_mul_of_nonneg_left havgNorm (by positivity)
      _ = (d : ℝ) * cubeLpNorm Q ∞ xi * X := by ring
  refine ⟨hreg, ?_⟩
  unfold scaleNormalizedPositiveBesovVectorNormTwo
  exact add_le_add havgEuclidean hsemi

/-- Corrected-flux cutoff pairing for an arbitrary nonzero `H¹` boundary
difference.  The coefficient dependence is entirely in the weak-flux RHS;
the cutoff product is priced by the scale-free `W¹,² -> B¹_{2,∞}` embedding
and the summable geometric loss below exponent one. -/
theorem exists_abs_correctedFlux_h1CutoffPairing_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
        (w : H1Function (openCubeSet Q))
        {eta : Vec d → ℝ} {B : ℝ},
        0 < s → s < 1 → ForceBesovRegularity Q s g →
        ContDiff ℝ (⊤ : ℕ∞) eta → HasCompactSupport eta →
        tsupport eta ⊆ openCubeSet Q → 0 ≤ B →
        MemLp (scalarCutoffGradientField eta) ∞ (normalizedCubeMeasure Q) →
        (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
          (fun x => scalarCutoffGradientField eta x i)) →
        (∀ i : Fin d, ∀ z ∈ cubeSet Q,
          ‖fderiv ℝ (fun x => scalarCutoffGradientField eta x i) z‖ ≤ B) →
        Integrable (fun x =>
          vecDot (forcedSolutionCorrectedFluxField Q a g u x)
            (w.toFun x • scalarCutoffGradientField eta x))
          (normalizedCubeMeasure Q) →
        Integrable (fun x =>
          vecDot (forcedSolutionCorrectedFluxField Q a g u x)
            ((cubeAverage Q w.toFun) • scalarCutoffGradientField eta x))
          (normalizedCubeMeasure Q) →
        let Gs : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹)
        let X : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
        let Y : ℝ := cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => euclideanNorm (w.grad x))
        let P : ℝ :=
          (d : ℝ) * cubeLpNorm Q ∞ (scalarCutoffGradientField eta) * X +
            2 * (cubeScaleFactor Q * B * (Gs * X) +
              cubeLpNorm Q ∞ (scalarCutoffGradientField eta) *
                (cubeScaleFactor Q * Gs *
                  (cubeBesovW12EmbeddingConstant d * Y)))
        |cubeAverage Q (fun x =>
          vecDot (forcedSolutionCorrectedFluxField Q a g u x)
            (w.toFun x • scalarCutoffGradientField eta x))| ≤
          C * (weakFluxWithRHSRHS C Q a s g u +
              boundaryNegativeToL2Factor (2 * s) *
                boundaryNormalizedEuclideanL2 Q g) * P := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_abs_correctedFlux_pairing_le_weakFlux_mul_positiveBesov d
  refine ⟨C, hC, ?_⟩
  intro Q a s g u w eta B hs hs1 hg heta hetaCompact hetaSupport hB
    hxiLp hxi hderiv hmain hconst
  dsimp only
  let xi : Vec d → Vec d := scalarCutoffGradientField eta
  let Gs : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹)
  let X : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
  let Y : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (w.grad x))
  let P : ℝ := (d : ℝ) * cubeLpNorm Q ∞ xi * X +
    2 * (cubeScaleFactor Q * B * (Gs * X) +
      cubeLpNorm Q ∞ xi *
        (cubeScaleFactor Q * Gs * (cubeBesovW12EmbeddingConstant d * Y)))
  have hproduct := centeredH1CutoffProduct_positiveBesovBudget
    (Q := Q) (s := s) w xi hB hxiLp hxi hderiv hs1
  have hprodReg : ForceBesovRegularity Q s
      (fun x => cubeFluctuation Q w.toFun x • xi x) := by
    simpa only [xi, cubeFluctuation] using hproduct.1
  have hprodNorm : scaleNormalizedPositiveBesovVectorNormTwo Q s
      (fun x => cubeFluctuation Q w.toFun x • xi x) ≤ P := by
    simpa only [xi, Gs, X, Y, P, cubeFluctuation] using hproduct.2
  have hP : 0 ≤ P := by
    have hGs : 0 ≤ Gs := by dsimp [Gs]; exact Real.sqrt_nonneg _
    have hX : 0 ≤ X := by dsimp [X]; exact cubeLpNorm_nonneg Q 2 _
    have hY : 0 ≤ Y := by dsimp [Y]; exact cubeLpNorm_nonneg Q 2 _
    have hxiNorm : 0 ≤ cubeLpNorm Q ∞ xi := cubeLpNorm_nonneg Q ∞ xi
    have hK : 0 ≤ cubeBesovW12EmbeddingConstant d :=
      cubeBesovW12EmbeddingConstant_nonneg d
    dsimp only [P]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hxiNorm) hX)
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
            (mul_nonneg hGs hX))
          (mul_nonneg hxiNorm
            (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hGs)
              (mul_nonneg hK hY)))))
  have hcenter :=
    cubeAverage_correctedFlux_scalar_smul_cutoffGradient_eq_centered
      u hg w.toFun heta hetaCompact hetaSupport hmain hconst
  have hbound := hpair u hs hs1 hg hprodReg hP hprodNorm
  rw [hcenter]
  simpa only [xi, cubeFluctuation, P, Gs, X, Y] using hbound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
