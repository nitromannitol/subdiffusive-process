module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.StepSixGapPower

@[expose] public section

/-!
# Hölder Step 6: reading scalar cutoff energy as a vector `L²` norm

The boundary Caccioppoli argument returns a normalized scalar energy average.  The
frozen Hölder row is written as the normalized Euclidean `L²` norm of
`sqrt(a_L) grad u`.  These lemmas provide the exact deterministic conversion.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

/-- Pointwise scalar-energy identity under the normalized vector `L²` readout. -/
theorem vectorNormalizedL2On_sqrt_smul_eq_sqrt_volumeAverage
    {d : ℕ} (W : Set (Vec d)) (a : Vec d → ℝ) (v : Vec d → Vec d)
    (ha : ∀ x, 0 ≤ a x) :
    vectorNormalizedL2On W (fun x ↦ Real.sqrt (a x) • v x) =
      Real.sqrt (volumeAverage W (fun x ↦ a x * vecNormSq (v x))) := by
  unfold vectorNormalizedL2On normalizedL2On
  congr 1
  apply congrArg (volumeAverage W)
  funext x
  change euclideanNorm (Real.sqrt (a x) • v x) ^ 2 =
    a x * vecNormSq (v x)
  rw [euclideanNorm_smul, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, euclideanNorm_sq, Real.sq_sqrt (ha x)]

/-- Monotone readout of a scalar normalized-energy bound. -/
theorem vectorNormalizedL2On_sqrt_smul_le_of_volumeAverage_le
    {d : ℕ} (W : Set (Vec d)) (a : Vec d → ℝ) (v : Vec d → Vec d)
    {B : ℝ} (ha : ∀ x, 0 ≤ a x)
    (havg : volumeAverage W (fun x ↦ a x * vecNormSq (v x)) ≤ B) :
    vectorNormalizedL2On W (fun x ↦ Real.sqrt (a x) • v x) ≤ Real.sqrt B := by
  rw [vectorNormalizedL2On_sqrt_smul_eq_sqrt_volumeAverage W a v ha]
  exact Real.sqrt_le_sqrt havg

/-- Specialization to the positive GMC cutoff coefficient. -/
theorem vectorNormalizedL2On_sqrt_aCutoff_eq
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (W : Set (Vec d)) (u : H1Function W) :
    vectorNormalizedL2On W
        (fun x ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) •
          u.grad x) =
      Real.sqrt (volumeAverage W (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x))) := by
  exact vectorNormalizedL2On_sqrt_smul_eq_sqrt_volumeAverage W
    (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) u.grad
    (fun x ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
