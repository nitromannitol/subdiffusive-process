module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalSplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Composition

@[expose] public section

/-!
# The physical boundary residual mean

The zero trace of `u - h` on the ambient cube controls its mean on a
well-placed boundary cube by the gradient on the next boundary window.  This
is the coefficient-free first half of the parent-mean estimate used in the
harmonic-approximation boundary row.

This is the boundary zero-set Poincaré step.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The physical residual mean on a well-placed boundary cube is controlled
by the residual gradient on the next boundary window.  The factor is written
with the literal physical volume so that multiplication by the manuscript's
`3^(-2k)` weight cancels the scale exactly in the next pricing step. -/
theorem abs_volumeAverage_physicalResidual_le_boundaryWindowGradient
    {m k : ℤ} {q : Vec d}
    (u h : H1Function (openCubeSet (originCube d m)))
    (rho : H10Function (openCubeSet (originCube d m)))
    (hval : ∀ x, u.toFun x = h.toFun x + rho.toH1Function.toFun x)
    (hkm : k ≤ m) (hq : q ∈ cube d m)
    (hnot : ¬ translatedCube d (k - 1) q ⊆ cube d m) :
    let c := Section6ExcessDecay.wellPlacedCentre q m k
    let P := translatedCube d k c
    let W := translatedCube d (k + 1) q ∩ cube d m
    |volumeAverage P (fun x ↦ u.toFun x - h.toFun x)| ≤
      projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
          Real.sqrt ((volume P).toReal) *
        ∑ j : Fin d,
          (eLpNorm (fun x ↦ rho.grad x j) 2
            (volume.restrict W)).toReal := by
  classical
  dsimp only
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  let P : Set (Vec d) := translatedCube d k c
  let W : Set (Vec d) := translatedCube d (k + 1) q ∩ cube d m
  have hPsub : P ⊆ W := by
    have hbase :=
      Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_truncatedCube
        (d := d) (m := m) (j := k + 1) q hq (by simpa using hkm)
    rw [show k + 1 - 1 = k by ring] at hbase
    exact hbase
  have hPmeas : MeasurableSet P := by
    dsimp [P]
    exact Section6Schauder.measurableSet_translatedCube d k c
  have hPtop : volume P ≠ ⊤ := by
    dsimp [P]
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet, volume_translateSet_eq]
    exact (volume_openCubeSet_lt_top (originCube d k)).ne
  have hPpos : 0 < (volume P).toReal := by
    dsimp [P]
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d k)
  have hrhoP : MemLp rho.toFun 2 (volume.restrict P) :=
    rho.toH1Function.memL2.mono_measure
      (Measure.restrict_mono_set volume
        (hPsub.trans (Section6ExcessDecay.truncatedCube_subset_cube d m (k + 1) q)))
  have hrhoW : MemLp rho.toFun 2 (volume.restrict W) :=
    rho.toH1Function.memL2.mono_measure
      (Measure.restrict_mono_set volume
        (Section6ExcessDecay.truncatedCube_subset_cube d m (k + 1) q))
  let : IsFiniteMeasure (volume.restrict P) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hPtop⟩
  have hresidual : (fun x ↦ u.toFun x - h.toFun x) = rho.toFun := by
    funext x
    rw [hval x]
    ring
  have hmean : |volumeAverage P rho.toFun| ≤ normalizedL2On P rho.toFun := by
    exact Section6Iteration.abs_volumeAverage_le_normalizedL2On
      hPmeas hPpos (hrhoP.integrable (by norm_num)) hrhoP.integrable_sq
  have hdict : normalizedL2On P rho.toFun =
      (eLpNorm rho.toFun 2 (volume.restrict P)).toReal /
        Real.sqrt ((volume P).toReal) :=
    Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div hrhoP
  have hmonoENN : eLpNorm rho.toFun 2 (volume.restrict P) ≤
      eLpNorm rho.toFun 2 (volume.restrict W) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hPsub)
  have hmono : (eLpNorm rho.toFun 2 (volume.restrict P)).toReal ≤
      (eLpNorm rho.toFun 2 (volume.restrict W)).toReal :=
    ENNReal.toReal_mono hrhoW.eLpNorm_ne_top hmonoENN
  have hpoin := eLpNorm_le_projectedBoundaryWindowPoincare hnot rho
  have hsqrt0 : 0 ≤ Real.sqrt ((volume P).toReal) := Real.sqrt_nonneg _
  rw [hresidual]
  refine hmean.trans ?_
  rw [hdict]
  calc
    (eLpNorm rho.toFun 2 (volume.restrict P)).toReal /
          Real.sqrt ((volume P).toReal) ≤
        (eLpNorm rho.toFun 2 (volume.restrict W)).toReal /
          Real.sqrt ((volume P).toReal) :=
      div_le_div_of_nonneg_right hmono hsqrt0
    _ ≤
        (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k *
          ∑ j : Fin d,
            (eLpNorm (fun x ↦ rho.grad x j) 2
              (volume.restrict W)).toReal) /
          Real.sqrt ((volume P).toReal) :=
      div_le_div_of_nonneg_right hpoin hsqrt0
    _ = projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
          Real.sqrt ((volume P).toReal) *
        ∑ j : Fin d,
          (eLpNorm (fun x ↦ rho.grad x j) 2
            (volume.restrict W)).toReal := by ring

/-- Squared, manuscript-weighted form of the preceding boundary Poincare
reduction.  No coefficient estimate is used here: the coefficient-dependent
task is now exactly the price of the residual-gradient window on the right. -/
theorem physicalResidualMean_weighted_le_boundaryWindowGradient
    {m k : ℤ} {q : Vec d}
    (u h : H1Function (openCubeSet (originCube d m)))
    (rho : H10Function (openCubeSet (originCube d m)))
    (hval : ∀ x, u.toFun x = h.toFun x + rho.toH1Function.toFun x)
    (hkm : k ≤ m) (hq : q ∈ cube d m)
    (hnot : ¬ translatedCube d (k - 1) q ⊆ cube d m)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    let c := Section6ExcessDecay.wellPlacedCentre q m k
    let P := translatedCube d k c
    let W := translatedCube d (k + 1) q ∩ cube d m
    sigma * Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
          volumeAverage P (fun x ↦ u.toFun x - h.toFun x) ^ 2 ≤
      sigma * Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
        (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
            Real.sqrt ((volume P).toReal) *
          ∑ j : Fin d,
            (eLpNorm (fun x ↦ rho.grad x j) 2
              (volume.restrict W)).toReal) ^ 2 := by
  classical
  dsimp only
  have hmean := abs_volumeAverage_physicalResidual_le_boundaryWindowGradient
    u h rho hval hkm hq hnot
  have hsq : volumeAverage
        (translatedCube d k
          (Section6ExcessDecay.wellPlacedCentre q m k))
        (fun x ↦ u.toFun x - h.toFun x) ^ 2 ≤
      (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
          Real.sqrt ((volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
        ∑ j : Fin d,
          (eLpNorm (fun x ↦ rho.grad x j) 2
            (volume.restrict
              (translatedCube d (k + 1) q ∩ cube d m))).toReal) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hmean 2
  exact mul_le_mul_of_nonneg_left hsq
    (mul_nonneg hsigma (Real.rpow_nonneg (by norm_num) _))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
