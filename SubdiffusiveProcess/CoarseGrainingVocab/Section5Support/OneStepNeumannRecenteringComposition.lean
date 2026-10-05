module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedRecentering
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannHessianPackage

@[expose] public section

/-!
# Weak-Hessian composition for Neumann interior recentering

The large-cube Neumann solution is recentered on an interior translated cube
by subtracting the canonical translated Neumann solution.  The difference is
harmonic.  This file supplies the missing deterministic composition step: weak
Hessians of the translated local solution and of the harmonic remainder add to
a weak Hessian of the restricted large solution, and the literal `B_z`
observable is subadditive under this decomposition.

-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Weak Hessians add under addition of `H¹` functions. -/
noncomputable def weakHessianAdd {d : ℕ} {U : Set (Vec d)}
    {u v : H1Function U}
    (Hu : HasWeakHessianOn U u) (Hv : HasWeakHessianOn U v) :
    HasWeakHessianOn U (u + v) where
  hess := fun i j x => Hu.hess i j x + Hv.hess i j x
  hess_memL2 := fun i j => (Hu.hess_memL2 i j).add (Hv.hess_memL2 i j)
  weak_second := by
    intro i j phi hphi hphiCompact hphiSub
    have hDu := Hu.weak_second i j phi hphi hphiCompact hphiSub
    have hDv := Hv.weak_second i j phi hphi hphiCompact hphiSub
    have htest : MemLp
        (fun x => (fderiv ℝ phi x) (basisVec j)) 2
        (volumeMeasureOn U) := by
      have hcont : Continuous fun x => (fderiv ℝ phi x) (basisVec j) :=
        (hphi.continuous_fderiv (by norm_num)).clm_apply continuous_const
      have hsupp : HasCompactSupport fun x =>
          (fderiv ℝ phi x) (basisVec j) := by
        apply HasCompactSupport.mono' (hphiCompact.fderiv ℝ)
        intro x hx
        apply subset_tsupport (fderiv ℝ phi)
        rw [Function.mem_support] at hx ⊢
        intro hzero
        apply hx
        rw [hzero]
        simp
      simpa [volumeMeasureOn] using
        hcont.memLp_of_hasCompactSupport hsupp |>.restrict U
    have huInt : IntegrableOn
        (fun x => u.grad x i * (fderiv ℝ phi x) (basisVec j)) U := by
      simpa [IntegrableOn, volumeMeasureOn, mul_comm] using
        (memLp_one_iff_integrable.mp ((u.gradMemL2 i).fun_mul htest))
    have hvInt : IntegrableOn
        (fun x => v.grad x i * (fderiv ℝ phi x) (basisVec j)) U := by
      simpa [IntegrableOn, volumeMeasureOn, mul_comm] using
        (memLp_one_iff_integrable.mp ((v.gradMemL2 i).fun_mul htest))
    have hphiTwo : MemLp phi 2 (volumeMeasureOn U) := by
      simpa [volumeMeasureOn] using
        hphi.continuous.memLp_of_hasCompactSupport hphiCompact |>.restrict U
    have hHuInt : IntegrableOn (fun x => Hu.hess i j x * phi x) U := by
      simpa [IntegrableOn, volumeMeasureOn, mul_comm] using
        (memLp_one_iff_integrable.mp ((Hu.hess_memL2 i j).fun_mul hphiTwo))
    have hHvInt : IntegrableOn (fun x => Hv.hess i j x * phi x) U := by
      simpa [IntegrableOn, volumeMeasureOn, mul_comm] using
        (memLp_one_iff_integrable.mp ((Hv.hess_memL2 i j).fun_mul hphiTwo))
    calc
      ∫ x in U, (u + v).grad x i * (fderiv ℝ phi x) (basisVec j)
          ∂volume =
          ∫ x in U,
            (u.grad x i * (fderiv ℝ phi x) (basisVec j) +
              v.grad x i * (fderiv ℝ phi x) (basisVec j)) ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            simp only [H1Function.add_grad, Pi.add_apply]
            ring
      _ = ∫ x in U, u.grad x i * (fderiv ℝ phi x) (basisVec j) ∂volume +
          ∫ x in U, v.grad x i * (fderiv ℝ phi x) (basisVec j) ∂volume :=
            integral_add huInt hvInt
      _ = -∫ x in U, Hu.hess i j x * phi x ∂volume +
          -∫ x in U, Hv.hess i j x * phi x ∂volume := by
            rw [hDu, hDv]
      _ = -∫ x in U,
          (Hu.hess i j x + Hv.hess i j x) * phi x ∂volume := by
            rw [show (fun x => (Hu.hess i j x + Hv.hess i j x) * phi x) =
                fun x => Hu.hess i j x * phi x + Hv.hess i j x * phi x by
              funext x; ring,
              integral_add hHuInt hHvInt]
            ring

/-- Transfer the sum witness to any `H¹` representative whose gradient is
the same sum.  This is the form needed after restricting a large Neumann
solution: its value representative need not be definitionally the sum of the
local solution and the harmonic remainder, while its gradient is exactly
that sum. -/
noncomputable def weakHessianOfGradEqAdd {d : ℕ} {U : Set (Vec d)}
    {u v w : H1Function U}
    (hgrad : u.grad = fun x => v.grad x + w.grad x)
    (Hv : HasWeakHessianOn U v) (Hw : HasWeakHessianOn U w) :
    HasWeakHessianOn U u where
  hess := fun i j x => Hv.hess i j x + Hw.hess i j x
  hess_memL2 := fun i j => (Hv.hess_memL2 i j).add (Hw.hess_memL2 i j)
  weak_second := by
    intro i j
    have hsum := (weakHessianAdd Hv Hw).weak_second i j
    simpa only [H1Function.add_grad, Pi.add_apply, hgrad,
      weakHessianAdd] using hsum

/-- The normalized coordinate-sum Hessian size is subadditive under the
canonical sum witness. -/
theorem oneStepCellNormalizedHessianSize_add_le
    {d : ℕ} (R : TriadicCube d) {u v : H1Function (openCubeSet R)}
    (Hu : HasWeakHessianOn (openCubeSet R) u)
    (Hv : HasWeakHessianOn (openCubeSet R) v) :
    oneStepCellNormalizedHessianSize R (weakHessianAdd Hu Hv) ≤
      oneStepCellNormalizedHessianSize R Hu +
        oneStepCellNormalizedHessianSize R Hv := by
  unfold oneStepCellNormalizedHessianSize
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _
    (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R)) _)
  unfold HasWeakHessianOn.hessianCoordL2NormSum
  calc
    ∑ i : Fin d, ∑ j : Fin d,
        ‖(weakHessianAdd Hu Hv).hessCoordToScalarL2 i j‖ ≤
        ∑ i : Fin d, ∑ j : Fin d,
          (‖Hu.hessCoordToScalarL2 i j‖ + ‖Hv.hessCoordToScalarL2 i j‖) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      change ‖Homogenization.toScalarL2 ((Hu.hess_memL2 i j).add
          (Hv.hess_memL2 i j))‖ ≤ _
      have heq : Homogenization.toScalarL2 ((Hu.hess_memL2 i j).add
            (Hv.hess_memL2 i j)) =
          Hu.hessCoordToScalarL2 i j + Hv.hessCoordToScalarL2 i j := by
        apply Lp.ext
        filter_upwards [coeFn_toScalarL2 (Hu.hess_memL2 i j),
          coeFn_toScalarL2 (Hv.hess_memL2 i j),
          coeFn_toScalarL2 ((Hu.hess_memL2 i j).add
            (Hv.hess_memL2 i j)),
          Lp.coeFn_add (Hu.hessCoordToScalarL2 i j)
            (Hv.hessCoordToScalarL2 i j)] with x hu hv hsum hadd
        rw [hsum]
        rw [hadd]
        exact (congrArg₂ (· + ·) hu hv).symm
      rw [heq]
      exact norm_add_le _ _
    _ = (∑ i : Fin d, ∑ j : Fin d, ‖Hu.hessCoordToScalarL2 i j‖) +
        ∑ i : Fin d, ∑ j : Fin d, ‖Hv.hessCoordToScalarL2 i j‖ := by
      simp only [Finset.sum_add_distrib]

/-- The literal cell `B` observable is subadditive for the recombined weak
Hessian. -/
theorem oneStepCellB_add_le
    {d : ℕ} (R : TriadicCube d) {u v : H1Function (openCubeSet R)}
    (Hu : HasWeakHessianOn (openCubeSet R) u)
    (Hv : HasWeakHessianOn (openCubeSet R) v) :
    oneStepCellB R (weakHessianAdd Hu Hv) ≤ oneStepCellB R Hu + oneStepCellB R Hv := by
  unfold oneStepCellB
  have hside := cubeScaleFactor_nonneg R
  calc
    cubeScaleFactor R * oneStepCellNormalizedHessianSize R (weakHessianAdd Hu Hv) ≤
        cubeScaleFactor R *
          (oneStepCellNormalizedHessianSize R Hu +
            oneStepCellNormalizedHessianSize R Hv) :=
      mul_le_mul_of_nonneg_left
        (oneStepCellNormalizedHessianSize_add_le R Hu Hv) hside
    _ = cubeScaleFactor R * oneStepCellNormalizedHessianSize R Hu +
        cubeScaleFactor R * oneStepCellNormalizedHessianSize R Hv := by ring

/-- Literal `B_z` triangle inequality for a gradient-level recentering.
This is the exact deterministic interface used by the Neumann nesting: the
large solution is the translated local solution plus the harmonic remainder
at the gradient level. -/
theorem oneStepCellB_le_of_grad_eq_add
    {d : ℕ} (R : TriadicCube d) {u v w : H1Function (openCubeSet R)}
    (hgrad : u.grad = fun x => v.grad x + w.grad x)
    (Hv : HasWeakHessianOn (openCubeSet R) v)
    (Hw : HasWeakHessianOn (openCubeSet R) w) :
    oneStepCellB R (weakHessianOfGradEqAdd hgrad Hv Hw) ≤
      oneStepCellB R Hv + oneStepCellB R Hw := by
  simpa only [weakHessianOfGradEqAdd] using!
    oneStepCellB_add_le R Hv Hw

/-- Specialization to the actual Neumann nested-recentring identity.  Given
weak-Hessian realizations of the stationary translated solution and of the
harmonic remainder on a common interior carrier, their restrictions produce
a weak Hessian of the restricted large-cube solution, with the literal cell
`B` bounded by the sum of the two pieces. -/
theorem exists_oneStepNeumannAxisLargeRestriction_cellB_le_local_add_remainder
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p z : Vec d)
    (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h)
    (V : Set (Vec d))
    (uLocal uRemainder : H1Function V)
    (huLocal : uLocal.grad =
      (oneStepNeumannAxisLocalSolution M n h omega p z m hh).grad)
    (huRemainder : uRemainder.grad =
      (oneStepNeumannAxisRemainder M n h omega p z K m hsub hh).grad)
    (Hlocal : HasWeakHessianOn V uLocal)
    (Hremainder : HasWeakHessianOn V uRemainder)
    (R : TriadicCube d)
    (hRaxis : openCubeSet R ⊆
      axisCube (oneStepCenteredAxisCorner z m)
        (cubeScaleFactor (originCube d m)))
    (hRV : openCubeSet R ⊆ V) :
    ∃ Hlarge : HasWeakHessianOn (openCubeSet R)
        ((oneStepNeumannAxisLargeRestriction
          M n h omega p z K m hsub hh).restrict
            (isOpen_openCubeSet R) hRaxis),
      oneStepCellB R Hlarge ≤
        oneStepCellB R
          (Hlocal.restrict (isOpen_openCubeSet R) hRV) +
        oneStepCellB R
          (Hremainder.restrict (isOpen_openCubeSet R) hRV) := by
  let uLargeR : H1Function (openCubeSet R) :=
    (oneStepNeumannAxisLargeRestriction
      M n h omega p z K m hsub hh).restrict
        (isOpen_openCubeSet R) hRaxis
  let uLocalR : H1Function (openCubeSet R) :=
    uLocal.restrict (isOpen_openCubeSet R) hRV
  let uRemainderR : H1Function (openCubeSet R) :=
    uRemainder.restrict (isOpen_openCubeSet R) hRV
  let HlocalR : HasWeakHessianOn (openCubeSet R) uLocalR :=
    Hlocal.restrict (isOpen_openCubeSet R) hRV
  let HremainderR : HasWeakHessianOn (openCubeSet R) uRemainderR :=
    Hremainder.restrict (isOpen_openCubeSet R) hRV
  have hgrad : uLargeR.grad =
      fun x => uLocalR.grad x + uRemainderR.grad x := by
    funext x
    apply funext
    intro i
    change
      (oneStepNeumannAxisLargeRestriction
          M n h omega p z K m hsub hh).grad x i =
        uLocal.grad x i + uRemainder.grad x i
    rw [congrFun huLocal x, congrFun huRemainder x]
    simp only [oneStepNeumannAxisRemainder, H1Function.sub_grad,
      Pi.sub_apply]
    ring
  let Hlarge : HasWeakHessianOn (openCubeSet R) uLargeR :=
    weakHessianOfGradEqAdd hgrad HlocalR HremainderR
  refine ⟨Hlarge, ?_⟩
  simpa only [Hlarge, HlocalR, HremainderR, uLargeR, uLocalR,
    uRemainderR] using
      oneStepCellB_le_of_grad_eq_add R hgrad HlocalR HremainderR

/-- Eliminate a harmonic-remainder budget after sending the recentering gap
to infinity.  This is the scalar limit used after the nested Neumann
composition: the local Dirichlet payload remains and the harmonic correction
vanishes geometrically. -/
theorem le_of_forall_le_add_one_third_pow_four
    {X D C : ℝ}
    (hbound : ∀ N : ℕ,
      X ≤ D + C * (((1 : ℝ) / 3) ^ N) ^ (4 : ℕ)) :
    X ≤ D := by
  have hpow : Filter.Tendsto (fun N : ℕ => ((1 : ℝ) / 3) ^ N)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hright : Filter.Tendsto
      (fun N : ℕ => D + C * (((1 : ℝ) / 3) ^ N) ^ (4 : ℕ))
      Filter.atTop (nhds D) := by
    simpa using tendsto_const_nhds.add ((hpow.pow 4).const_mul C)
  exact ge_of_tendsto hright (Filter.Eventually.of_forall hbound)

/-- `ENNReal` form of the vanishing-remainder close, matching the moment
budgets produced by the measurable cell layer.  Finiteness of the common
multiplier excludes the indeterminate `∞ * 0` branch. -/
theorem ennreal_le_of_forall_le_add_one_third_pow_four
    {X D C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ N : ℕ,
      X ≤ D + C * (((3 : ℝ≥0∞)⁻¹) ^ N) ^ (4 : ℕ)) :
    X ≤ D := by
  have hpow : Filter.Tendsto
      (fun N : ℕ => ((((3 : ℝ≥0∞)⁻¹) ^ (4 : ℕ)) ^ N))
      Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (pow_lt_one₀ (zero_le) (ENNReal.inv_lt_one.2 (by norm_num)) (by norm_num))
  have hright : Filter.Tendsto
      (fun N : ℕ => D + C * (((3 : ℝ≥0∞)⁻¹) ^ N) ^ (4 : ℕ))
      Filter.atTop (nhds D) := by
    have hmul := ENNReal.Tendsto.const_mul hpow (Or.inr hC)
    convert tendsto_const_nhds.add hmul using 1
    · funext N
      congr 2
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    · simp
  exact ge_of_tendsto hright (Filter.Eventually.of_forall hbound)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
