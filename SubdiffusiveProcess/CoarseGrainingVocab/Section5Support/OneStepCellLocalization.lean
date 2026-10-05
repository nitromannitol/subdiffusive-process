module

public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1
public import Homogenization.Sobolev.Foundations.CubeCoerciveH1
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicInteriorHessian
public import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry

@[expose] public section

/-!
# Cell localization for the one-step comparison fields

This module isolates the deterministic Poincare part of the cell estimates at
`l.one.step.upper` and `l.one.step.lower`.  A weak Hessian on a parent cube controls the
normalized `L²` oscillation of its gradient on every triadic descendant.  The
constant is the scale-correct unit-cube coercive constant already supplied by
CoarseGraining.

The proof deliberately uses the library's weak-Hessian and descendant-cube
interfaces rather than introducing a smooth surrogate.  It is common to the
Dirichlet and Neumann comparisons: only the construction and quantitative
bound of the weak Hessian differ between those two lanes.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Coordinate-sum representative of the paper's normalized cell
oscillation `A_z = ‖P - (P)_R‖_{L̲²(R)}`.  The coordinate sum is equivalent to
the Euclidean norm up to a dimension-only constant and is the native output
of the weak-Hessian Poincare API. -/
def oneStepCellGradientOscillation {d : ℕ} (R : TriadicCube d)
    (u : H1Function (openCubeSet R)) : ℝ :=
  ∑ i : Fin d,
    cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => u.grad x i)

/-- Coordinate-sum normalized `L²` Hessian size on one cell. -/
def oneStepCellNormalizedHessianSize {d : ℕ} (R : TriadicCube d)
    {u : H1Function (openCubeSet R)}
    (H : HasWeakHessianOn (openCubeSet R) u) : ℝ :=
  ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) * H.hessianCoordL2NormSum

/-- Coordinate-sum normalized `L⁴` Hessian size on one cell, the manuscript's
interior `W^{2,4}` carrier for `B_z`. -/
def oneStepCellHessianFourSize {d : ℕ} (R : TriadicCube d)
    {u : H1Function (openCubeSet R)}
    (H : HasWeakHessianOn (openCubeSet R) u) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    cubeLpNorm R (4 : ℝ≥0∞) (fun x => H.hess i j x)

theorem oneStepCellNormalizedHessianSize_nonneg {d : ℕ}
    (R : TriadicCube d) {u : H1Function (openCubeSet R)}
    (H : HasWeakHessianOn (openCubeSet R) u) :
    0 ≤ oneStepCellNormalizedHessianSize R H := by
  exact mul_nonneg
    (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R)) _)
    H.hessianCoordL2NormSum_nonneg

/-- On the normalized cube measure, the `L⁴` Hessian size dominates the
`L²` Hessian size.  This is the Lyapunov step used after the printed interior
`W^{2,4}` estimate. -/
theorem oneStepCellNormalizedHessianSize_le_hessianFourSize
    {d : ℕ} (R : TriadicCube d) {u : H1Function (openCubeSet R)}
    (H : HasWeakHessianOn (openCubeSet R) u)
    (hH4 : ∀ i j : Fin d, MeasureTheory.MemLp (fun x => H.hess i j x)
      (4 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    oneStepCellNormalizedHessianSize R H ≤
      oneStepCellHessianFourSize R H := by
  let : MeasureTheory.IsProbabilityMeasure (normalizedCubeMeasure R) := by
    refine ⟨?_⟩
    simp [normalizedCubeMeasure_apply_univ R]
  unfold oneStepCellNormalizedHessianSize oneStepCellHessianFourSize
  rw [HasWeakHessianOn.hessianCoordL2NormSum, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hH2 : MeasureTheory.MemLp (fun x => H.hess i j x)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memL2On_openCubeSet_normalizedCubeMeasure (H.hess_memL2 i j)
  calc
    (cubeVolume R)⁻¹ ^ (1 / 2 : ℝ) * ‖H.hessCoordToScalarL2 i j‖ =
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => H.hess i j x) := by
      exact (cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openCubeSet
        R hH2).symm
    _ ≤ cubeLpNorm R (4 : ℝ≥0∞) (fun x => H.hess i j x) := by
      unfold cubeLpNorm
      exact ENNReal.toReal_mono (hH4 i j).eLpNorm_ne_top
        (MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
          (by norm_num : (2 : ℝ≥0∞) ≤ 4))

theorem oneStepCellGradientOscillation_nonneg {d : ℕ}
    (R : TriadicCube d) (u : H1Function (openCubeSet R)) :
    0 ≤ oneStepCellGradientOscillation R u := by
  exact Finset.sum_nonneg fun i _ => cubeBesovOscillation_nonneg R 2 _

/-- Smooth form of the printed cell Poincare estimate.  A uniform Hessian
bound `B` on the closed cell controls the coordinate-sum normalized gradient
oscillation by `d * side(R) * B`.  The one-step argument obtains `B` from the
interior harmonic and differentiated-forcing estimates. -/
theorem oneStepCellGradientOscillation_le_of_contDiff_gradient_bound
    {d : ℕ} (R : TriadicCube d) (u : H1Function (openCubeSet R))
    {B : ℝ} (hB : 0 ≤ B)
    (hgradLp : ∀ i : Fin d, MeasureTheory.MemLp (fun x => u.grad x i) ∞
      (normalizedCubeMeasure R))
    (hgradSmooth : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => u.grad x i))
    (hHessian : ∀ (i : Fin d) (x : Vec d), x ∈ cubeSet R →
      ‖fderiv ℝ (fun y => u.grad y i) x‖ ≤ B) :
    oneStepCellGradientOscillation R u ≤
      (d : ℝ) * cubeScaleFactor R * B := by
  unfold oneStepCellGradientOscillation
  calc
    ∑ i : Fin d, cubeBesovOscillation R (2 : ℝ≥0∞)
        (fun x => u.grad x i) ≤
        ∑ _i : Fin d, cubeScaleFactor R * B := by
      exact Finset.sum_le_sum fun i _ =>
        cubeBesovOscillation_two_le_cubeScaleFactor_mul_of_contDiff_bound
          R hB (hgradLp i) (hgradSmooth i) (hHessian i)
    _ = (d : ℝ) * cubeScaleFactor R * B := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring



theorem oneStepCellGradientOscillation_le_localHessian
    {d : ℕ} {Q R : TriadicCube d} {depth : ℕ}
    {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hR : R ∈ descendantsAtDepth Q depth) :
    oneStepCellGradientOscillation R (u.restrictToOpenSubcube hR) ≤
      ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        (cubeScaleFactor R *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        (H.restrict (isOpen_openCubeSet R)
          (openCubeSet_subset_of_mem_descendantsAtDepth hR)
          ).hessianCoordL2NormSum := by
  let HR : HasWeakHessianOn (openCubeSet R) (u.restrictToOpenSubcube hR) :=
    H.restrict (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
  let C : ℝ := ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
    (cubeScaleFactor R *
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R)) _)
      (mul_nonneg (by
        simpa [cubeScaleFactor] using
          (le_of_lt (zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale)))
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg)
  have hcoord : ∀ i : Fin d,
      cubeBesovOscillation R (2 : ℝ≥0∞)
          (fun x => (u.restrictToOpenSubcube hR).grad x i) ≤
        C * ‖(HR.gradCoordH1Function i).gradToVectorL2‖ := by
    intro i
    have hi := HR.cubeBesovOscillation_gradCoord_le_volumeInvRpowHalf_mul_coerciveConst
      i (scaledTranslatedCubeMeanZeroH1CoerciveEstimate R)
    simpa only [C,
      scaledTranslatedCubeMeanZeroH1CoerciveEstimate_constant] using hi
  calc
    oneStepCellGradientOscillation R (u.restrictToOpenSubcube hR) ≤
        ∑ i : Fin d, C *
          ‖(HR.gradCoordH1Function i).gradToVectorL2‖ := by
      exact Finset.sum_le_sum fun i _ => hcoord i
    _ ≤ ∑ i : Fin d, C *
          (∑ j : Fin d, ‖HR.hessCoordToScalarL2 i j‖) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left
          (HR.gradCoordH1Function_gradToVectorL2_norm_le_rowCoordL2NormSum i) hC
    _ = C * HR.hessianCoordL2NormSum := by
      simp only [HasWeakHessianOn.hessianCoordL2NormSum, Finset.mul_sum]
    _ = ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        (cubeScaleFactor R *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        (H.restrict (isOpen_openCubeSet R)
          (openCubeSet_subset_of_mem_descendantsAtDepth hR)
          ).hessianCoordL2NormSum := by rfl

/-- Scale-transparent version of the cell Poincare estimate: normalized
gradient oscillation is at most the cell side times the normalized Hessian
size, with the dimension-only unit-cube coercive constant. -/
theorem oneStepCellGradientOscillation_le_normalizedHessian
    {d : ℕ} (R : TriadicCube d) {u : H1Function (openCubeSet R)}
    (H : HasWeakHessianOn (openCubeSet R) u) :
    oneStepCellGradientOscillation R u ≤
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        cubeScaleFactor R * oneStepCellNormalizedHessianSize R H := by
  let C0 : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).constant
  let A : ℝ := ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
    (cubeScaleFactor R * C0)
  have hA : 0 ≤ A := by
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R)) _)
      (mul_nonneg (cubeScaleFactor_nonneg R)
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg)
  have hcoord : ∀ i : Fin d,
      cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => u.grad x i) ≤
        A * ‖(H.gradCoordH1Function i).gradToVectorL2‖ := by
    intro i
    have hi := H.cubeBesovOscillation_gradCoord_le_volumeInvRpowHalf_mul_coerciveConst
      i (scaledTranslatedCubeMeanZeroH1CoerciveEstimate R)
    simpa only [A, C0,
      scaledTranslatedCubeMeanZeroH1CoerciveEstimate_constant] using hi
  calc
    oneStepCellGradientOscillation R u ≤
        ∑ i : Fin d, A * ‖(H.gradCoordH1Function i).gradToVectorL2‖ := by
      exact Finset.sum_le_sum fun i _ => hcoord i
    _ ≤ ∑ i : Fin d, A *
          (∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left
          (H.gradCoordH1Function_gradToVectorL2_norm_le_rowCoordL2NormSum i) hA
    _ = A * H.hessianCoordL2NormSum := by
      simp only [HasWeakHessianOn.hessianCoordL2NormSum, Finset.mul_sum]
    _ = C0 * cubeScaleFactor R * oneStepCellNormalizedHessianSize R H := by
      unfold oneStepCellNormalizedHessianSize
      ring

/-- The printed `W^{2,4}`-to-cell-oscillation implication. -/
theorem oneStepCellGradientOscillation_le_hessianFourSize
    {d : ℕ} (R : TriadicCube d) {u : H1Function (openCubeSet R)}
    (H : HasWeakHessianOn (openCubeSet R) u)
    (hH4 : ∀ i j : Fin d, MeasureTheory.MemLp (fun x => H.hess i j x)
      (4 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    oneStepCellGradientOscillation R u ≤
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        cubeScaleFactor R * oneStepCellHessianFourSize R H := by
  calc
    oneStepCellGradientOscillation R u ≤
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
          cubeScaleFactor R * oneStepCellNormalizedHessianSize R H :=
      oneStepCellGradientOscillation_le_normalizedHessian R H
    _ ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
          cubeScaleFactor R * oneStepCellHessianFourSize R H := by
      exact mul_le_mul_of_nonneg_left
        (oneStepCellNormalizedHessianSize_le_hessianFourSize R H hH4)
        (mul_nonneg
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
          (cubeScaleFactor_nonneg R))



theorem oneStepCellGradientOscillation_le_parentScale_add_forcing
    {d : ℕ} (Q R : TriadicCube d) {u : H1Function (openCubeSet R)}
    (H : HasWeakHessianOn (openCubeSet R) u)
    {Creg parentGradient forcingDerivative : ℝ}
    (hH : oneStepCellNormalizedHessianSize R H ≤
      Creg * (cubeScaleFactor Q)⁻¹ * parentGradient +
        Creg * forcingDerivative) :
    oneStepCellGradientOscillation R u ≤
      ((originCubeMeanZeroH1CoerciveEstimate d 0).constant * Creg) *
          (cubeScaleFactor R * (cubeScaleFactor Q)⁻¹) * parentGradient +
        ((originCubeMeanZeroH1CoerciveEstimate d 0).constant * Creg) *
          cubeScaleFactor R * forcingDerivative := by
  let C0 : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).constant
  have hC0 : 0 ≤ C0 :=
    (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  calc
    oneStepCellGradientOscillation R u ≤
        C0 * cubeScaleFactor R * oneStepCellNormalizedHessianSize R H :=
      oneStepCellGradientOscillation_le_normalizedHessian R H
    _ ≤ C0 * cubeScaleFactor R *
        (Creg * (cubeScaleFactor Q)⁻¹ * parentGradient +
          Creg * forcingDerivative) := by
      exact mul_le_mul_of_nonneg_left hH
        (mul_nonneg hC0 (cubeScaleFactor_nonneg R))
    _ = (C0 * Creg) * (cubeScaleFactor R * (cubeScaleFactor Q)⁻¹) *
          parentGradient +
        (C0 * Creg) * cubeScaleFactor R * forcingDerivative := by ring

/-- The cell-localization estimate after inserting the PDE interior-Hessian
bound.  This is the precise interface used by the printed one-step argument:
the two terms on the right are respectively the parent-gradient contribution
and the differentiated fresh-shell forcing contribution. -/
theorem oneStepCellGradientOscillation_le_parent_add_forcing
    {d : ℕ} {Q R : TriadicCube d} {depth : ℕ}
    {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hR : R ∈ descendantsAtDepth Q depth)
    {parentEnergy forcingEnergy : ℝ}
    (hH : (H.restrict (isOpen_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR)
        ).hessianCoordL2NormSum ≤ parentEnergy + forcingEnergy) :
    oneStepCellGradientOscillation R (u.restrictToOpenSubcube hR) ≤
      ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        (cubeScaleFactor R *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        parentEnergy +
      ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        (cubeScaleFactor R *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        forcingEnergy := by
  let C : ℝ := ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
    (cubeScaleFactor R *
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R)) _)
      (mul_nonneg (by
        simpa [cubeScaleFactor] using
          (le_of_lt (zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale)))
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg)
  calc
    oneStepCellGradientOscillation R (u.restrictToOpenSubcube hR) ≤
        C * (H.restrict (isOpen_openCubeSet R)
          (openCubeSet_subset_of_mem_descendantsAtDepth hR)
          ).hessianCoordL2NormSum :=
      oneStepCellGradientOscillation_le_localHessian H hR
    _ ≤ C * (parentEnergy + forcingEnergy) :=
      mul_le_mul_of_nonneg_left hH hC
    _ = C * parentEnergy + C * forcingEnergy := by ring
    _ = ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          (cubeScaleFactor R *
            (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
          parentEnergy +
        ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          (cubeScaleFactor R *
            (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        forcingEnergy := by rfl

/-- Local Hessian-to-cell-oscillation estimate when the Hessian is carried on
an arbitrary open ambient set containing the cell.  This is the form needed
after the library's fixed-radius interior regularity theorem, whose carrier is
the half-parent cube rather than another triadic cube. -/
theorem oneStepCellGradientOscillation_restrict_le_localHessian
    {d : ℕ} {U : Set (Vec d)}
    (R : TriadicCube d) {u : H1Function U}
    (H : HasWeakHessianOn U u) (hRU : openCubeSet R ⊆ U) :
    oneStepCellGradientOscillation R
        (u.restrict (isOpen_openCubeSet R) hRU) ≤
      ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        (cubeScaleFactor R *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        (H.restrict (isOpen_openCubeSet R) hRU).hessianCoordL2NormSum := by
  let uR : H1Function (openCubeSet R) :=
    u.restrict (isOpen_openCubeSet R) hRU
  let HR : HasWeakHessianOn (openCubeSet R) uR :=
    H.restrict (isOpen_openCubeSet R) hRU
  let C : ℝ := ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
    (cubeScaleFactor R *
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R)) _)
      (mul_nonneg (by
        simpa [cubeScaleFactor] using
          (le_of_lt (zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale)))
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg)
  have hcoord : ∀ i : Fin d,
      cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => uR.grad x i) ≤
        C * ‖(HR.gradCoordH1Function i).gradToVectorL2‖ := by
    intro i
    have hi := HR.cubeBesovOscillation_gradCoord_le_volumeInvRpowHalf_mul_coerciveConst
      i (scaledTranslatedCubeMeanZeroH1CoerciveEstimate R)
    simpa only [C,
      scaledTranslatedCubeMeanZeroH1CoerciveEstimate_constant] using hi
  calc
    oneStepCellGradientOscillation R uR ≤
        ∑ i : Fin d, C * ‖(HR.gradCoordH1Function i).gradToVectorL2‖ := by
      exact Finset.sum_le_sum fun i _ => hcoord i
    _ ≤ ∑ i : Fin d, C *
          (∑ j : Fin d, ‖HR.hessCoordToScalarL2 i j‖) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left
          (HR.gradCoordH1Function_gradToVectorL2_norm_le_rowCoordL2NormSum i) hC
    _ = C * HR.hessianCoordL2NormSum := by
      simp only [HasWeakHessianOn.hessianCoordL2NormSum, Finset.mul_sum]
    _ = ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        (cubeScaleFactor R *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        (H.restrict (isOpen_openCubeSet R) hRU).hessianCoordL2NormSum := by rfl

/-- Restricting the carrier of a weak Hessian does not increase the sum of
its coordinate `L²` norms. -/
theorem hessianCoordL2NormSum_restrict_le
    {d : ℕ} {U V : Set (Vec d)} {u : H1Function U}
    (H : HasWeakHessianOn U u) (hVopen : IsOpen V) (hVU : V ⊆ U) :
    (H.restrict hVopen hVU).hessianCoordL2NormSum ≤
      H.hessianCoordL2NormSum := by
  unfold HasWeakHessianOn.hessianCoordL2NormSum
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [HasWeakHessianOn.hessCoordToScalarL2, Homogenization.toScalarL2,
    MeasureTheory.Lp.norm_toLp]
  rw [HasWeakHessianOn.hessCoordToScalarL2, Homogenization.toScalarL2,
    MeasureTheory.Lp.norm_toLp]
  exact ENNReal.toReal_mono (H.hess_memL2 i j).ne
    (MeasureTheory.eLpNorm_mono_measure _
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU))

/-- Weak-Hessian harmonic localization on an arbitrary interior cell.  The
parent inverse scale comes from the library's fixed-radius interior theorem;
the displayed cell-volume normalization remains explicit.  The manuscript's
sharper normalized-parent estimate additionally needs an interior pointwise
Hessian (or equivalent reverse-volume) bound. -/
theorem exists_harmonic_oneStepCellGradientOscillation_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q R : TriadicCube d) (u : H1Function (openCubeSet Q))
        (_hharmonic : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0))
        (hRQ : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ)),
        ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
          uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
          oneStepCellGradientOscillation R
              (uS.restrict (isOpen_openCubeSet R) hRQ) ≤
            ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
              (cubeScaleFactor R *
                (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
              (C * (cubeScaleFactor Q)⁻¹ *
                u.gradientCoordL2NormSum) := by
  obtain ⟨C, hC, hregularity⟩ :=
    CubeCalderonZygmund.exists_harmonic_innerHalf_hessian_energy_bound d
  refine ⟨C, hC, ?_⟩
  intro Q R u hharmonic hRQ
  obtain ⟨uS, huSfun, huSgrad, H, hH⟩ := hregularity Q u hharmonic
  refine ⟨uS, huSfun, huSgrad, ?_⟩
  let A : ℝ := ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
    (cubeScaleFactor R *
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R)) _)
      (mul_nonneg (by
        simpa [cubeScaleFactor] using
          (le_of_lt (zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale)))
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg)
  calc
    oneStepCellGradientOscillation R
        (uS.restrict (isOpen_openCubeSet R) hRQ) ≤
      A * (H.restrict (isOpen_openCubeSet R) hRQ).hessianCoordL2NormSum := by
        exact oneStepCellGradientOscillation_restrict_le_localHessian
          R H hRQ
    _ ≤ A * H.hessianCoordL2NormSum := by
      exact mul_le_mul_of_nonneg_left
        (hessianCoordL2NormSum_restrict_le H
          (isOpen_openCubeSet R) hRQ) hA
    _ ≤ A * (C * (cubeScaleFactor Q)⁻¹ *
        u.gradientCoordL2NormSum) :=
      mul_le_mul_of_nonneg_left hH hA
    _ = ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        (cubeScaleFactor R *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        (C * (cubeScaleFactor Q)⁻¹ *
          u.gradientCoordL2NormSum) := by rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
