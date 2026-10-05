module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.HomogenizationError
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentFactorization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.CombineAssemblySeams
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceScale

@[expose] public section

/-!
# Descending the Section 4 homogenization error to a one-step cell

This file records the exact consequence of the proved Section 4 headline
which is available before the cutoff-sensitivity comparison. It deliberately keeps the
geometric descendant loss visible.  The subsequent Section 3 sensitivity
step is responsible for replacing this direct high-cutoff descent by a
uniform cell estimate.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

private theorem originCube_pred_mem_childCubes_originCube {d : ℕ} (t : ℤ) :
    originCube d (t - 1) ∈ childCubes (originCube d t) := by
  rw [mem_childCubes_iff]
  refine ⟨fun _ => (1 : Fin 3), ?_⟩
  simp only [originCube]
  apply congrArg₂ TriadicCube.mk
  · rfl
  · funext i
    norm_num

private theorem originCube_sub_nat_mem_descendantsAtDepth {d : ℕ}
    (t : ℤ) : ∀ depth : ℕ,
    originCube d (t - (depth : ℤ)) ∈ descendantsAtDepth (originCube d t) depth
  | 0 => by simp
  | depth + 1 => by
      rw [descendantsAtDepth_succ]
      refine Finset.mem_biUnion.mpr ⟨originCube d (t - (depth : ℤ)),
        originCube_sub_nat_mem_descendantsAtDepth t depth, ?_⟩
      convert originCube_pred_mem_childCubes_originCube (d := d)
        (t - (depth : ℤ)) using 1
      congr 1
      push_cast
      ring

/-- The smaller centered cube is a descendant of the larger centered cube at
its literal scale. -/
theorem originCube_mem_descendantsAtScale_of_nat_le {d : ℕ} {j K : ℕ}
    (hjK : j ≤ K) :
    originCube d (j : ℤ) ∈ descendantsAtScale (originCube d (K : ℤ)) (j : ℤ) := by
  have hscale : (j : ℤ) ≤ (originCube d (K : ℤ)).scale := by
    simpa [originCube] using (show (j : ℤ) ≤ (K : ℤ) by exact_mod_cast hjK)
  rw [descendantsAtScale_eq_descendantsAtDepth _ hscale]
  have hsub : ((K : ℤ) - (j : ℤ)).toNat = K - j := by omega
  change originCube d (j : ℤ) ∈ descendantsAtDepth (originCube d (K : ℤ))
    (((K : ℤ) - (j : ℤ)).toNat)
  rw [hsub]
  have hkj : (K : ℤ) - ((K - j : ℕ) : ℤ) = (j : ℤ) := by omega
  simpa only [hkj] using originCube_sub_nat_mem_descendantsAtDepth (d := d) (K : ℤ) (K - j)

private theorem translatePotentialSample_zero {d : ℕ} (omega : Sample d) :
    translatePotentialSample (0 : Vec d) omega = omega := by
  funext k
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  change omega k (x + 0) = omega k x
  rw [add_zero]

/-- At zero translation the translated error wrapper is the ordinary
same-cutoff error on the indicated centered cube. -/
theorem translatedHomogenizationErrorRandom_zero_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L K : ℕ) (s : ℝ)
    (omega : Sample d) :
    translatedHomogenizationErrorRandom M L K 0 s 1 omega =
      homogenizationErrorRandom M L K s omega := by
  unfold translatedHomogenizationErrorRandom homogenizationErrorRandom
    paperHomogenizationErrorDefault
  rw [translatePotentialSample_zero]
  norm_num

/-- Direct high-cutoff descent from its root cube to a smaller origin cell.
The factor `3^(s (L-j))` is exact and is intentionally not hidden. -/
theorem translatedHomogenizationErrorRandom_zero_le_root
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L j : ℕ) (s : ℝ)
    (hjL : j ≤ L) (omega : Sample d) :
    translatedHomogenizationErrorRandom M L j 0 s 1 omega ≤
      ENNReal.ofReal (Real.rpow 3 (s * ((L - j : ℕ) : ℝ))) *
        homogenizationErrorRandom M L L s omega := by
  rw [translatedHomogenizationErrorRandom_zero_eq]
  let F := aCutoffFamily M L omega
  have hdesc : originCube d (j : ℤ) ∈
      descendantsAtScale (originCube d (L : ℤ)) (j : ℤ) :=
    originCube_mem_descendantsAtScale_of_nat_le hjL
  have h := paperHomogenizationErrorDefault_descendant_le
    F (ahom M L) (s := s) hdesc
  have hscaleJ : (originCube d (j : ℤ)).scale = (j : ℤ) := by
    simp [originCube]
  have hscaleL : (originCube d (L : ℤ)).scale = (L : ℤ) := by
    simp [originCube]
  have hgap : (((L : ℤ) - (j : ℤ)).toNat : ℕ) = L - j := by omega
  simpa only [homogenizationErrorRandom, hscaleJ, hscaleL, hgap,
    aCutoffFamily] using! h

/-- Paper-`L^p` form of the direct high-cutoff descent. -/
theorem translatedHomogenizationErrorRandom_zero_lpnorm_le_root
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L j : ℕ)
    {p s : ℝ} (hp : 0 < p) (hjL : j ≤ L) :
    paperENNRealLpNorm M.P.toMeasure p
        (translatedHomogenizationErrorRandom M L j 0 s 1) ≤
      ENNReal.ofReal (Real.rpow 3 (s * ((L - j : ℕ) : ℝ))) *
        paperENNRealLpNorm M.P.toMeasure p
          (homogenizationErrorRandom M L L s) := by
  have hmono := paperENNRealLpNorm_mono_ae M.P.toMeasure hp.le
    (Filter.Eventually.of_forall fun omega =>
      translatedHomogenizationErrorRandom_zero_le_root M L j s hjL omega)
  calc
    _ ≤ paperENNRealLpNorm M.P.toMeasure p (fun omega =>
        ENNReal.ofReal (Real.rpow 3 (s * ((L - j : ℕ) : ℝ))) *
          homogenizationErrorRandom M L L s omega) := hmono
    _ = _ := by
      have hmeas : Measurable (homogenizationErrorRandom M L L s) := by
        have ht :=
          SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.measurable_translatedHomogenizationErrorRandom_one
            M L L 0 (s := s)
        have heq : translatedHomogenizationErrorRandom M L L 0 s 1 =
            homogenizationErrorRandom M L L s := by
          funext omega
          exact translatedHomogenizationErrorRandom_zero_eq M L L s omega
        rwa [heq] at ht
      exact paperENNRealLpNorm_const_mul_eq M.P.toMeasure hp _ _ hmeas

/-- Literal source-scale specialization of the direct descent.  This theorem
is useful diagnostically: it shows exactly why direct use of the high-cutoff
headline is insufficient for the uniform Step 2 factor budget--the loss also
contains the block length `h`.  The manuscript removes that loss with the
separate cutoff-sensitivity comparison. -/
theorem sourceScale_highCutoff_homogenizationError_lpnorm_le_root
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    {p s : ℝ} (hp : 0 < p)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n) :
    paperENNRealLpNorm M.P.toMeasure p
        (translatedHomogenizationErrorRandom M (n + h)
          (oneStepLocalizationScale n M.delta) 0 s 1) ≤
      ENNReal.ofReal (Real.rpow 3
          (s * ((h + oneStepLocalizationDepth M.delta : ℕ) : ℝ))) *
        paperENNRealLpNorm M.P.toMeasure p
          (homogenizationErrorRandom M (n + h) (n + h) s) := by
  have hj : oneStepLocalizationScale n M.delta ≤ n + h := by
    exact (Nat.sub_le _ _).trans (Nat.le_add_right n h)
  have hbound := translatedHomogenizationErrorRandom_zero_lpnorm_le_root
    M (n + h) (oneStepLocalizationScale n M.delta) (s := s) hp hj
  rw [oneStep_highCutoff_sub_localizationScale hsource] at hbound
  exact hbound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
