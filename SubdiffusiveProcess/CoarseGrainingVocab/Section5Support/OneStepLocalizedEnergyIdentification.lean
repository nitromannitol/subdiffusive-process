module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLocalizedGluing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellMomentAggregation
public import Homogenization.Deterministic.WeakNormInterfacesComponentwise

@[expose] public section

/-!
# Localized cell energies in the manuscript `A_z/B_z` carrier

This module is the deterministic absorption.  The selected Dirichlet and
Neumann cell solutions already provide the exact energy identities.  Once
the Besov duality estimate bounds the corresponding pairing by

`C * sqrt(ellipticity) * sqrt(energy) * positiveBesovSize`,

the self-bounding energy is absorbed and the interpolation estimate for the
positive Besov size is inserted in the literal
`A^2 + A^(3/2) B^(1/2)` carrier.

Keeping the two analytic inputs explicit makes this module usable with the
`q = 1` negative / `q = infinity` positive pairing from the source, without
silently replacing it by the parallel `q = 2` argument.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Real-valued version of `A + A^(3/4) B^(1/4)`.  The nested square roots
avoid any convention-sensitive fractional-power coercions. -/
def oneStepCellBesovSize (A B : ℝ) : ℝ :=
  A + Real.sqrt (A * Real.sqrt (A * B))

theorem oneStepCellBesovSize_nonneg {A B : ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) :
    0 ≤ oneStepCellBesovSize A B := by
  unfold oneStepCellBesovSize
  positivity

/-- Squaring the manuscript interpolation size produces, up to the harmless
factor two, its literal Step 2 cell error. -/
theorem oneStepCellBesovSize_sq_le_two_mul_error {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    oneStepCellBesovSize A B ^ 2 ≤
      2 * oneStepCellBesovError A B := by
  let X : ℝ := Real.sqrt (A * Real.sqrt (A * B))
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hinner : 0 ≤ A * Real.sqrt (A * B) :=
    mul_nonneg hA (Real.sqrt_nonneg _)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hXsq : X ^ 2 = A * Real.sqrt A * Real.sqrt B := by
    dsimp [X]
    rw [Real.sq_sqrt hinner, Real.sqrt_mul hA]
    ring
  have hcross : 2 * A * X ≤ A ^ 2 + X ^ 2 :=
    two_mul_le_add_sq A X
  unfold oneStepCellBesovSize oneStepCellBesovError
  change (A + X) ^ 2 ≤ 2 * (A ^ 2 + A * Real.sqrt A * Real.sqrt B)
  rw [← hXsq]
  nlinarith

/-- Exact `q = 1` negative / `q = infinity` positive Besov pairing used in
the manuscript.  The parent-scale weights cancel, leaving only the explicit
dimension-and-exponent constant. -/
theorem oneStep_abs_pairing_fluctuation_le_of_qOne_besov_bounds
    {d : ℕ} (Q : TriadicCube d) {s Bu Bg : ℝ}
    (flux F : Vec d → Vec d)
    (hs : 0 < s)
    (hflux : MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hdual : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x ↦ cubeFluctuationVec Q F x i) ≤
        cubeBesovScaleWeight s Q * Bg) :
    |cubeAverage Q (fun x ↦
        vecDot (flux x) (cubeFluctuationVec Q F x))| ≤
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s) * Bu * Bg := by
  have hraw :=
    abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_dualTestBounds
      Q s flux F hs hflux hF hBg hneg hdual
  have hweights :
      cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q = 1 :=
    cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
  calc
    |cubeAverage Q (fun x ↦
        vecDot (flux x) (cubeFluctuationVec Q F x))| ≤
        (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
          (cubeBesovScaleWeight s Q * Bg)) := hraw
    _ = (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s) * Bu * Bg := by
      calc
        (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg)) =
          ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)) *
            (cubeBesovScaleWeight (-s) Q *
              cubeBesovScaleWeight s Q) * Bu * Bg := by ring
        _ = _ := by rw [hweights]; ring



theorem oneStep_volumeAverage_openCubeSet_eq_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = cubeAverage Q f := by
  calc
    volumeAverage (openCubeSet Q) f =
        (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, f x ∂volume := by
      unfold volumeAverage
      rw [volume_openCubeSet_toReal]
    _ = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x ∂volume := by
      rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = cubeAverage Q f := rfl

/-- A centered datum can be used literally in the fluctuation slot of the
componentwise Besov pairing. -/
theorem oneStep_abs_volumeAverage_pairing_le_of_qOne_besov_bounds
    {d : ℕ} (Q : TriadicCube d) {s Bu Bg : ℝ}
    (flux F : Vec d → Vec d)
    (hs : 0 < s)
    (hflux : MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hFcenter : cubeAverageVec Q F = 0)
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hdual : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x ↦ cubeFluctuationVec Q F x i) ≤
        cubeBesovScaleWeight s Q * Bg) :
    |volumeAverage (openCubeSet Q) (fun x ↦ vecDot (F x) (flux x))| ≤
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s) * Bu * Bg := by
  have hfluct : cubeFluctuationVec Q F = F := by
    funext x i
    simp only [cubeFluctuationVec_apply]
    rw [hFcenter]
    simp
  rw [oneStep_volumeAverage_openCubeSet_eq_cubeAverage]
  have hpair := oneStep_abs_pairing_fluctuation_le_of_qOne_besov_bounds
    Q flux F hs hflux hF hBg hneg hdual
  rw [hfluct] at hpair
  simpa only [vecDot_comm] using hpair

/-- Convert the source's literal positive `B^(s)_(2,infinity)` component
bound into the dual-test hypothesis used above.  In particular, this does
not pass through the stronger depth-square-summed `q = 2` package. -/
theorem oneStep_qOne_dualTest_of_positiveTop_component_bounds
    {d : ℕ} (Q : TriadicCube d) {s Bg : ℝ}
    (F : Vec d → Vec d)
    (hpositive : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N
          (fun x ↦ cubeFluctuationVec Q F x i) ≤
        cubeBesovScaleWeight s Q * Bg) :
    ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x ↦ cubeFluctuationVec Q F x i) ≤
        cubeBesovScaleWeight s Q * Bg := by
  intro i N
  have hconj : cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have havg : cubeAverage Q
      (fun x ↦ cubeFluctuationVec Q F x i) = 0 := by
    simpa [cubeFluctuation_component_eq_cubeFluctuationVec_component Q F i] using
      cubeAverage_cubeFluctuation Q (fun x ↦ F x i)
  rw [cubeBesovDualTestNorm_of_conjExponent_eq_top
    Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N _ hconj]
  rw [cubeBesovPartialNormTop_eq_cubeBesovPartialSeminormTop_of_cubeAverage_eq_zero
    Q s (cubeBesovConjExponent (2 : ℝ≥0∞)) N _ havg, hpConj]
  exact hpositive i N

/-- Uniform control of every positive Besov depth controls every finite
`q = infinity` truncation. -/
theorem oneStep_cubeBesovPartialSeminormTop_le_of_depth_bounds
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → ℝ) {B : ℝ}
    (hdepth : ∀ j : ℕ, cubeBesovDepthSeminorm Q s p u j ≤ B) :
    ∀ N : ℕ, cubeBesovPartialSeminormTop Q s p N u ≤ B := by
  intro N
  unfold cubeBesovPartialSeminormTop
  apply Finset.sup'_le
  intro j _hj
  exact hdepth j

/-- Source-oriented form of the preceding conversion: a depthwise
`B^(s)_(2,infinity)` estimate for every coordinate of the centered datum is
enough for the `q = 1` duality theorem. -/
theorem oneStep_qOne_dualTest_of_positiveDepth_component_bounds
    {d : ℕ} (Q : TriadicCube d) {s Bg : ℝ}
    (F : Vec d → Vec d)
    (hdepth : ∀ i : Fin d, ∀ j : ℕ,
      cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞)
          (fun x ↦ cubeFluctuationVec Q F x i) j ≤
        cubeBesovScaleWeight s Q * Bg) :
    ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x ↦ cubeFluctuationVec Q F x i) ≤
        cubeBesovScaleWeight s Q * Bg := by
  apply oneStep_qOne_dualTest_of_positiveTop_component_bounds Q F
  intro i
  exact oneStep_cubeBesovPartialSeminormTop_le_of_depth_bounds
    Q s (2 : ℝ≥0∞) (fun x ↦ cubeFluctuationVec Q F x i) (hdepth i)

/-- Scalar absorption used by both localized cell estimates. -/
theorem oneStep_selfBoundedEnergy_le_sq
    {E C ellipticity positiveSize : ℝ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hP : 0 ≤ positiveSize)
    (hbound : E ≤ C * Real.sqrt ellipticity * Real.sqrt E * positiveSize) :
    E ≤ C ^ 2 * ellipticity * positiveSize ^ 2 := by
  let T : ℝ := C * Real.sqrt ellipticity * positiveSize
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hsqrt : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hsqrt_sq : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
  have hroot : Real.sqrt E ≤ T := by
    by_cases hz : Real.sqrt E = 0
    · simpa [hz] using hT
    · have hzpos : 0 < Real.sqrt E := lt_of_le_of_ne hsqrt (Ne.symm hz)
      have hbound' : (Real.sqrt E) ^ 2 ≤ T * Real.sqrt E := by
        rw [hsqrt_sq]
        simpa [T, mul_assoc, mul_left_comm, mul_comm] using hbound
      nlinarith
  calc
    E = (Real.sqrt E) ^ 2 := hsqrt_sq.symm
    _ ≤ T ^ 2 := pow_le_pow_left₀ hsqrt hroot 2
    _ = C ^ 2 * (Real.sqrt ellipticity) ^ 2 * positiveSize ^ 2 := by
      dsimp [T]
      ring
    _ = C ^ 2 * ellipticity * positiveSize ^ 2 := by
      rw [Real.sq_sqrt hell]

/-- Insert the manuscript interpolation error after the self-bound has been
absorbed. -/
theorem oneStep_selfBoundedEnergy_le_cellBesovError
    {E C ellipticity positiveSize A B : ℝ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hP : 0 ≤ positiveSize)
    (hbound : E ≤ C * Real.sqrt ellipticity * Real.sqrt E * positiveSize)
    (hinterp : positiveSize ^ 2 ≤ oneStepCellBesovError A B) :
    E ≤ C ^ 2 * ellipticity * oneStepCellBesovError A B := by
  have hbase := oneStep_selfBoundedEnergy_le_sq hE hC hell hP hbound
  exact hbase.trans (mul_le_mul_of_nonneg_left hinterp
    (mul_nonneg (sq_nonneg C) hell))

/-- Source-facing specialization where the positive Besov interpolation has
already been expressed in the exact `A_z/B_z` size. -/
theorem oneStep_selfBoundedEnergy_le_two_mul_cellBesovError
    {E C ellipticity A B : ℝ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : E ≤ C * Real.sqrt ellipticity * Real.sqrt E *
      oneStepCellBesovSize A B) :
    E ≤ 2 * C ^ 2 * ellipticity * oneStepCellBesovError A B := by
  have hbase := oneStep_selfBoundedEnergy_le_sq
    hE hC hell (oneStepCellBesovSize_nonneg hA hB) hbound
  calc
    E ≤ C ^ 2 * ellipticity * oneStepCellBesovSize A B ^ 2 := hbase
    _ ≤ C ^ 2 * ellipticity *
        (2 * oneStepCellBesovError A B) :=
      mul_le_mul_of_nonneg_left
        (oneStepCellBesovSize_sq_le_two_mul_error hA hB)
        (mul_nonneg (sq_nonneg C) hell)
    _ = 2 * C ^ 2 * ellipticity * oneStepCellBesovError A B := by ring

/-- The selected primal cell energy is exactly the self-pairing to which the
`B^{-1/4}_{2,1}`--`B^{1/4}_{2,infinity}` estimate is applied.  This theorem
performs the ensuing absorption and records the result directly in the
literal `A_z/B_z` error carrier. -/
theorem OneStepDirichletCellMinimizer.energy_le_cellBesovError
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {F : Vec d → Vec d} (X : OneStepDirichletCellMinimizer Q a F)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hF : MemVectorL2 (openCubeSet Q) F)
    {C ellipticity positiveSize A B : ℝ}
    (hE : 0 ≤ volumeAverage (openCubeSet Q) (fun x ↦
      vecDot (X.field x) (matVecMul (a x) (X.field x))))
    (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hP : 0 ≤ positiveSize)
    (hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (F x) (matVecMul (a x) (X.field x)))| ≤
        C * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.field x) (matVecMul (a x) (X.field x)))) *
          positiveSize)
    (hinterp : positiveSize ^ 2 ≤ oneStepCellBesovError A B) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.field x) (matVecMul (a x) (X.field x))) ≤
      C ^ 2 * ellipticity * oneStepCellBesovError A B := by
  let E : ℝ := volumeAverage (openCubeSet Q) (fun x ↦
    vecDot (X.field x) (matVecMul (a x) (X.field x)))
  have hidentity : E = volumeAverage (openCubeSet Q) (fun x ↦
      vecDot (F x) (matVecMul (a x) (X.field x))) := by
    unfold E volumeAverage
    rw [X.energy_identity hEll hF]
  have hself : E ≤ C * Real.sqrt ellipticity * Real.sqrt E * positiveSize := by
    calc
      E = volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (F x) (matVecMul (a x) (X.field x))) := hidentity
      _ ≤ |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (F x) (matVecMul (a x) (X.field x)))| := le_abs_self _
      _ ≤ C * Real.sqrt ellipticity * Real.sqrt E * positiveSize := hpair
  exact oneStep_selfBoundedEnergy_le_cellBesovError hE hC hell hP hself hinterp

/-- Ellipticity supplies the nonnegativity premise in the primal endpoint. -/
theorem OneStepDirichletCellMinimizer.energy_le_cellBesovError_of_elliptic
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {F : Vec d → Vec d} (X : OneStepDirichletCellMinimizer Q a F)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hF : MemVectorL2 (openCubeSet Q) F)
    {C ellipticity positiveSize A B : ℝ}
    (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hP : 0 ≤ positiveSize)
    (hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (F x) (matVecMul (a x) (X.field x)))| ≤
        C * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.field x) (matVecMul (a x) (X.field x)))) *
          positiveSize)
    (hinterp : positiveSize ^ 2 ≤ oneStepCellBesovError A B) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.field x) (matVecMul (a x) (X.field x))) ≤
      C ^ 2 * ellipticity * oneStepCellBesovError A B := by
  have hfield : MemVectorL2 (openCubeSet Q) X.field :=
    hF.add X.correction.toH1Function.grad_memVectorL2
  have hnonneg : 0 ≤ volumeAverage (openCubeSet Q) (fun x ↦
      vecDot (X.field x) (matVecMul (a x) (X.field x))) := by
    apply volumeAverage_nonneg_of_nonneg_on
      (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    simpa [coefficientEnergyDensity_eq_unsymmetrized] using
      coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll X.field x hx
  exact X.energy_le_cellBesovError hEll hF hnonneg hC hell hP hpair hinterp

/-- Literal primal Step 2 endpoint after the fractional interpolation has
been stated as `oneStepCellBesovSize A B`. -/
theorem OneStepDirichletCellMinimizer.energy_le_two_mul_cellBesovError
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {F : Vec d → Vec d} (X : OneStepDirichletCellMinimizer Q a F)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hF : MemVectorL2 (openCubeSet Q) F)
    {C ellipticity A B : ℝ}
    (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (F x) (matVecMul (a x) (X.field x)))| ≤
        C * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.field x) (matVecMul (a x) (X.field x)))) *
          oneStepCellBesovSize A B) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.field x) (matVecMul (a x) (X.field x))) ≤
      2 * C ^ 2 * ellipticity * oneStepCellBesovError A B := by
  have hfield : MemVectorL2 (openCubeSet Q) X.field :=
    hF.add X.correction.toH1Function.grad_memVectorL2
  have hE : 0 ≤ volumeAverage (openCubeSet Q) (fun x ↦
      vecDot (X.field x) (matVecMul (a x) (X.field x))) := by
    apply volumeAverage_nonneg_of_nonneg_on
      (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    simpa [coefficientEnergyDensity_eq_unsymmetrized] using
      coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll X.field x hx
  let E : ℝ := volumeAverage (openCubeSet Q) (fun x ↦
    vecDot (X.field x) (matVecMul (a x) (X.field x)))
  have hidentity : E = volumeAverage (openCubeSet Q) (fun x ↦
      vecDot (F x) (matVecMul (a x) (X.field x))) := by
    unfold E volumeAverage
    rw [X.energy_identity hEll hF]
  have hself : E ≤ C * Real.sqrt ellipticity * Real.sqrt E *
      oneStepCellBesovSize A B := by
    calc
      E = volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (F x) (matVecMul (a x) (X.field x))) := hidentity
      _ ≤ |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (F x) (matVecMul (a x) (X.field x)))| := le_abs_self _
      _ ≤ _ := hpair
  exact oneStep_selfBoundedEnergy_le_two_mul_cellBesovError
    hE hC hell hA hB hself

/-- Fully expanded primal cell estimate at the Besov interface.  The only
remaining analytic inputs are precisely the finite `q = 1` negative bound
for the corrected flux and the uniform positive dual-test bound for the
centered suffix datum. -/
theorem OneStepDirichletCellMinimizer.energy_le_of_qOne_besov_bounds
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {F : Vec d → Vec d} (X : OneStepDirichletCellMinimizer Q a F)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hFopen : MemVectorL2 (openCubeSet Q) F)
    {s ellipticity A B : ℝ}
    (hs : 0 < s) (hell : 0 ≤ ellipticity)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hflux : MemLp (fun x ↦ matVecMul (a x) (X.field x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hFcenter : cubeAverageVec Q F = 0)
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q s N
          (fun x ↦ matVecMul (a x) (X.field x)) ≤
        Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.field x) (matVecMul (a x) (X.field x)))))
    (hdual : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x ↦ cubeFluctuationVec Q F x i) ≤
        cubeBesovScaleWeight s Q * oneStepCellBesovSize A B) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.field x) (matVecMul (a x) (X.field x))) ≤
      2 * ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)) ^ 2 * ellipticity *
        oneStepCellBesovError A B := by
  let C : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpairRaw := oneStep_abs_volumeAverage_pairing_le_of_qOne_besov_bounds
    Q (fun x ↦ matVecMul (a x) (X.field x)) F hs hflux hF hFcenter
      (oneStepCellBesovSize_nonneg hA hB) hneg hdual
  have hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (F x) (matVecMul (a x) (X.field x)))| ≤
        C * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.field x) (matVecMul (a x) (X.field x)))) *
          oneStepCellBesovSize A B := by
    simpa only [C, mul_assoc] using hpairRaw
  exact X.energy_le_two_mul_cellBesovError hEll hFopen hC hell hA hB hpair

/-- Dual counterpart of
`OneStepDirichletCellMinimizer.energy_le_cellBesovError`.  The selected
Neumann energy identity identifies the inverse-coefficient flux energy with
the pairing against its prescribed centered datum. -/
theorem OneStepNeumannCellMinimizer.energy_le_cellBesovError
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {G : Vec d → Vec d} (X : OneStepNeumannCellMinimizer Q a G)
    {C ellipticity positiveSize A B : ℝ}
    (hE : 0 ≤ volumeAverage (openCubeSet Q) (fun x ↦
      vecDot (X.potential.toH1Function.grad x) (X.flux x)))
    (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hP : 0 ≤ positiveSize)
    (hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (G x) (X.potential.toH1Function.grad x))| ≤
        C * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x))) *
          positiveSize)
    (hinterp : positiveSize ^ 2 ≤ oneStepCellBesovError A B) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) ≤
      C ^ 2 * ellipticity * oneStepCellBesovError A B := by
  let E : ℝ := volumeAverage (openCubeSet Q) (fun x ↦
    vecDot (X.potential.toH1Function.grad x) (X.flux x))
  have hidentity : E = volumeAverage (openCubeSet Q) (fun x ↦
      vecDot (G x) (X.potential.toH1Function.grad x)) := by
    unfold E volumeAverage
    rw [X.energy_identity]
  have hself : E ≤ C * Real.sqrt ellipticity * Real.sqrt E * positiveSize := by
    calc
      E = volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (G x) (X.potential.toH1Function.grad x)) := hidentity
      _ ≤ |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (G x) (X.potential.toH1Function.grad x))| := le_abs_self _
      _ ≤ C * Real.sqrt ellipticity * Real.sqrt E * positiveSize := hpair
  exact oneStep_selfBoundedEnergy_le_cellBesovError hE hC hell hP hself hinterp

/-- Ellipticity supplies nonnegativity for the selected dual flux energy. -/
theorem OneStepNeumannCellMinimizer.energy_le_cellBesovError_of_elliptic
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {G : Vec d → Vec d} (X : OneStepNeumannCellMinimizer Q a G)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {C ellipticity positiveSize A B : ℝ}
    (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hP : 0 ≤ positiveSize)
    (hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (G x) (X.potential.toH1Function.grad x))| ≤
        C * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x))) *
          positiveSize)
    (hinterp : positiveSize ^ 2 ≤ oneStepCellBesovError A B) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) ≤
      C ^ 2 * ellipticity * oneStepCellBesovError A B := by
  have hnonneg : 0 ≤ volumeAverage (openCubeSet Q) (fun x ↦
      vecDot (X.potential.toH1Function.grad x) (X.flux x)) := by
    apply volumeAverage_nonneg_of_nonneg_on
      (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    change 0 ≤ vecDot (X.potential.toH1Function.grad x)
      (matVecMul (a x) (X.potential.toH1Function.grad x))
    simpa [coefficientEnergyDensity_eq_unsymmetrized] using
      coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll
        X.potential.toH1Function.grad x hx
  exact X.energy_le_cellBesovError hnonneg hC hell hP hpair hinterp

/-- Literal dual Step 2 endpoint after the same `A_z/B_z` interpolation. -/
theorem OneStepNeumannCellMinimizer.energy_le_two_mul_cellBesovError
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {G : Vec d → Vec d} (X : OneStepNeumannCellMinimizer Q a G)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {C ellipticity A B : ℝ}
    (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (G x) (X.potential.toH1Function.grad x))| ≤
        C * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x))) *
          oneStepCellBesovSize A B) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) ≤
      2 * C ^ 2 * ellipticity * oneStepCellBesovError A B := by
  have hE : 0 ≤ volumeAverage (openCubeSet Q) (fun x ↦
      vecDot (X.potential.toH1Function.grad x) (X.flux x)) := by
    apply volumeAverage_nonneg_of_nonneg_on
      (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    change 0 ≤ vecDot (X.potential.toH1Function.grad x)
      (matVecMul (a x) (X.potential.toH1Function.grad x))
    simpa [coefficientEnergyDensity_eq_unsymmetrized] using
      coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll
        X.potential.toH1Function.grad x hx
  let E : ℝ := volumeAverage (openCubeSet Q) (fun x ↦
    vecDot (X.potential.toH1Function.grad x) (X.flux x))
  have hidentity : E = volumeAverage (openCubeSet Q) (fun x ↦
      vecDot (G x) (X.potential.toH1Function.grad x)) := by
    unfold E volumeAverage
    rw [X.energy_identity]
  have hself : E ≤ C * Real.sqrt ellipticity * Real.sqrt E *
      oneStepCellBesovSize A B := by
    calc
      E = volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (G x) (X.potential.toH1Function.grad x)) := hidentity
      _ ≤ |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (G x) (X.potential.toH1Function.grad x))| := le_abs_self _
      _ ≤ _ := hpair
  exact oneStep_selfBoundedEnergy_le_two_mul_cellBesovError
    hE hC hell hA hB hself

/-- Fully expanded dual cell estimate at the same `q = 1`/`q = infinity`
interface.  Here the negative norm is carried by the selected Neumann
gradient and the positive datum is the centered flux fluctuation. -/
theorem OneStepNeumannCellMinimizer.energy_le_of_qOne_besov_bounds
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {G : Vec d → Vec d} (X : OneStepNeumannCellMinimizer Q a G)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {s ellipticity A B : ℝ}
    (hs : 0 < s) (hell : 0 ≤ ellipticity)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrad : MemLp X.potential.toH1Function.grad
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : MemLp G (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hGcenter : cubeAverageVec Q G = 0)
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q s N
          X.potential.toH1Function.grad ≤
        Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x))))
    (hdual : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x ↦ cubeFluctuationVec Q G x i) ≤
        cubeBesovScaleWeight s Q * oneStepCellBesovSize A B) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) ≤
      2 * ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)) ^ 2 * ellipticity *
        oneStepCellBesovError A B := by
  let C : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpairRaw := oneStep_abs_volumeAverage_pairing_le_of_qOne_besov_bounds
    Q X.potential.toH1Function.grad G hs hgrad hG hGcenter
      (oneStepCellBesovSize_nonneg hA hB) hneg hdual
  have hpair :
      |volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (G x) (X.potential.toH1Function.grad x))| ≤
        C * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x))) *
          oneStepCellBesovSize A B := by
    simpa only [C, mul_assoc] using hpairRaw
  exact X.energy_le_two_mul_cellBesovError hEll hC hell hA hB hpair

/-! ## Direct descendants-family readouts -/

/-- Apply the primal `A_z/B_z` energy estimate to the actual selected member
of a descendant family.  This is the term consumed by the finite patch
assembly. -/
theorem oneStepSelectedDirichletCell_energy_le_two_mul_cellBesovError
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) (F : TriadicCube d → Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ descendantsAtDepth Q j)
    {C ellipticity A B : ℝ}
    (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpair :
      |volumeAverage (openCubeSet R) (fun x ↦
          vecDot (F R x)
            (matVecMul (a x)
              ((oneStepSelectedDirichletCell a F hEll hF R hR).field x)))| ≤
        C * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet R) (fun x ↦
            vecDot
              ((oneStepSelectedDirichletCell a F hEll hF R hR).field x)
              (matVecMul (a x)
                ((oneStepSelectedDirichletCell a F hEll hF R hR).field x)))) *
          oneStepCellBesovSize A B) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot ((oneStepSelectedDirichletCell a F hEll hF R hR).field x)
          (matVecMul (a x)
            ((oneStepSelectedDirichletCell a F hEll hF R hR).field x))) ≤
      2 * C ^ 2 * ellipticity * oneStepCellBesovError A B := by
  exact (oneStepSelectedDirichletCell a F hEll hF R hR
    ).energy_le_two_mul_cellBesovError
      (hEll R hR) (hF R hR) hC hell hA hB hpair

/-- Dual selected-family counterpart used by the glued-flux assembly. -/
theorem oneStepSelectedNeumannCell_energy_le_two_mul_cellBesovError
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) (G : TriadicCube d → Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hG : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (G S))
    (hR : R ∈ descendantsAtDepth Q j)
    {C ellipticity A B : ℝ}
    (hC : 0 ≤ C) (hell : 0 ≤ ellipticity)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpair :
      |volumeAverage (openCubeSet R) (fun x ↦
          vecDot (G R x)
            ((oneStepSelectedNeumannCell a G hEll hG R hR
              ).potential.toH1Function.grad x))| ≤
        C * Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet R) (fun x ↦
            vecDot
              ((oneStepSelectedNeumannCell a G hEll hG R hR
                ).potential.toH1Function.grad x)
              ((oneStepSelectedNeumannCell a G hEll hG R hR).flux x))) *
          oneStepCellBesovSize A B) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot
          ((oneStepSelectedNeumannCell a G hEll hG R hR
            ).potential.toH1Function.grad x)
          ((oneStepSelectedNeumannCell a G hEll hG R hR).flux x)) ≤
      2 * C ^ 2 * ellipticity * oneStepCellBesovError A B := by
  exact (oneStepSelectedNeumannCell a G hEll hG R hR
    ).energy_le_two_mul_cellBesovError
      (hEll R hR) hC hell hA hB hpair

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
