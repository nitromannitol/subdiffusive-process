module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.EllipticityErrorAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ExponentComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.RawErrorFiniteness
public import SubdiffusiveProcess.Providers.Section2.GeneralCoarseGraining

@[expose] public section

/-!
# The paper `q = 2` error dominates the Chapter 2 error

This is the `q = 2` companion of
`ErrorComparison.ofReal_homogenizationErrorOnCube_le_paperHomogenizationError`.
It is needed because the Section 6 good event is written with the paper's
scalar-probe carrier, while the off-grid stability theorem is written with
Chapter 2's full-block carrier.

This is the carrier-conversion step used implicitly by
 before its local
ellipticity caps are read.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

private theorem summable_weight_mul_response_max
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {s : ℝ} (hs : 0 < s) :
    Summable fun l : ℕ => Ch02.geometricWeight s 2 l *
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q
        (Q.scale - (l : ℤ)) F a0 := by
  exact Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := 2) (C := Ch02.normalizedBlockResponseUniformBound Q F a0)
      (by linarith only [hs])
      (fun l => Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
        (sub_le_self _ (Int.natCast_nonneg l)) F a0)
      (fun l => Ch02.maxDescendantNormalizedBlockResponseAtScale_le_uniform Q
        (sub_le_self _ (Int.natCast_nonneg l)) F a0)

/-- The Chapter 2 `(infinity,2)` error is bounded, after `ofReal`, by the
paper scalar-probe `(infinity,2)` error. -/
theorem ofReal_homogenizationErrorOnCube_infinity_two_le_paper
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Ch02.TriadicCoeffFamily d)
    (hF : ∀ R, (F.coeffOn R).IsSymmetric) {s sigma : ℝ}
    (hs : 0 < s) (hsigma : 0 < sigma) :
    ENNReal.ofReal
        (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
          (scalarMatrix (d := d) sigma)) ≤
      paperHomogenizationError Q Q.scale s .infinity (.finite 2) F sigma := by
  have hscale : ∀ k : ℤ, k ≤ Q.scale →
      ENNReal.ofReal
          (Ch02.scaleResponseAtScale Q k .infinity F
          (scalarMatrix (d := d) sigma)) ^ (2 : ℕ) ≤
        (paperScaleResponseAtScale Q k .infinity F sigma) ^ (2 : ℝ) := by
    intro k hk
    have hmax : ENNReal.ofReal
        (Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
          (scalarMatrix (d := d) sigma)) ≤
        paperMaxDescendantProbeAtScale Q k F sigma := by
      by_cases htop : paperMaxDescendantProbeAtScale Q k F sigma = ⊤
      · simp [htop]
      · rw [ENNReal.ofReal_le_iff_le_toReal htop]
        apply Ch02.finsetSupReal_le (descendantsAtScale Q k)
          (descendantsAtScale_nonempty Q hk)
        intro R hR
        have hprobe :=
          SubdiffusiveProcess.Providers.Section2.normalizedBlockResponseMax_le_paperScalarProbeMax
            R F (hF R) hsigma
        have hprobe' : ENNReal.ofReal
            (Ch02.normalizedBlockResponseMax R F
              (scalarMatrix (d := d) sigma)) ≤
            paperMaxDescendantProbeAtScale Q k F sigma :=
          hprobe.trans (le_iSup
            (fun T : {T : TriadicCube d // T ∈ descendantsAtScale Q k} =>
              paperScalarProbeMax T.1 F sigma) ⟨R, hR⟩)
        exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hprobe'
    simp only [Ch02.scaleResponseAtScale_infinity_eq,
      paperScaleResponseAtScale]
    have hroot : ENNReal.ofReal
        (Real.rpow
          (Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
            (scalarMatrix (d := d) sigma)) (1 / 2 : ℝ)) ≤
        (paperMaxDescendantProbeAtScale Q k F sigma) ^ (1 / 2 : ℝ) := by
      calc
        ENNReal.ofReal (Real.rpow
            (Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
              (scalarMatrix (d := d) sigma)) (1 / 2 : ℝ)) =
            (ENNReal.ofReal
              (Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
                (scalarMatrix (d := d) sigma))) ^ (1 / 2 : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg
            (Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk F _)
            (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm
        _ ≤ (paperMaxDescendantProbeAtScale Q k F sigma) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hmax (by norm_num)
    calc
      ENNReal.ofReal
            (Ch02.scaleResponseAtScale Q k .infinity F
              (scalarMatrix (d := d) sigma)) ^ (2 : ℕ) ≤
          (paperScaleResponseAtScale Q k .infinity F sigma) ^ (2 : ℕ) :=
        pow_le_pow_left' hroot 2
      _ = (paperScaleResponseAtScale Q k .infinity F sigma) ^ (2 : ℝ) :=
        (ENNReal.rpow_natCast _ 2).symm
  have hE0 : 0 ≤ Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
      (scalarMatrix (d := d) sigma) :=
    LambdaStabilitySupport.homogenizationErrorOnCube_infinity_two_nonneg
      Q F (scalarMatrix (d := d) sigma) hs
  rw [← Real.sqrt_sq hE0, Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs F
    (scalarMatrix (d := d) sigma)]
  rw [show paperHomogenizationError Q Q.scale s .infinity (.finite 2) F sigma =
      (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
        (paperScaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F sigma) ^
          (2 : ℝ)) ^ (1 / 2 : ℝ) by
    simp [paperHomogenizationError, paperHomogenizationErrorFinite]]
  apply ENNReal.rpow_le_rpow
  · rw [ENNReal.ofReal_tsum_of_nonneg]
    · apply ENNReal.tsum_le_tsum
      intro l
      rw [ENNReal.ofReal_mul (by
        simpa [Ch02.geometricWeight_eq_old] using
          (Homogenization.geometricWeight_nonneg (s := s) (q := (2 : ℝ)) l
            (by positivity : 0 ≤ s * 2)))]
      have hk : Q.scale - (l : ℤ) ≤ Q.scale := sub_le_self _ (by positivity)
      rw [← Ch02.scaleResponseAtScale_infinity_sq_eq Q hk F
        (scalarMatrix (d := d) sigma), ENNReal.ofReal_pow]
      exact mul_le_mul' le_rfl (hscale _ hk)
      exact Ch02.scaleResponseAtScale_infinity_nonneg Q hk F _
    · intro l
      exact mul_nonneg
        (by simpa [Ch02.geometricWeight_eq_old] using
          (Homogenization.geometricWeight_nonneg (s := s) (q := (2 : ℝ)) l
            (by positivity : 0 ≤ s * 2)))
        (Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
          (sub_le_self _ (by positivity)) F _)
    · exact summable_weight_mul_response_max Q F
        (scalarMatrix (d := d) sigma) hs
  · norm_num

/-- On the frozen good event, the Chapter 2 full-block error of the translated
cutoff family is bounded by the literal real-valued Section 6 error.  The raw
paper error is finite here by the annular good-event budget, so no information
is lost through its `ENNReal.toReal` storage. -/
theorem homogenizationErrorOnCube_aCutoff_le_section6_of_goodEvent
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    {L m : ℕ} (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (hgood : omega ∈ goodEvent M none m z 1 s) :
    Ch02.HomogenizationErrorOnCube (originCube d (m : ℤ)) s
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (scalarMatrix (d := d)
          (tailCoefficientCubeAverage M L m (translatePotentialSample z omega))) ≤
      section6HomogenizationError M s L m omega z := by
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  have hsigma : 0 < tailCoefficientCubeAverage M L m
      (translatePotentialSample z omega) :=
    tailCoefficientCubeAverage_pos M L m (translatePotentialSample z omega)
  have hraw := ofReal_homogenizationErrorOnCube_infinity_two_le_paper
    (originCube d (m : ℤ))
    (aCutoffFamily M L (translatePotentialSample z omega))
    (fun R => (aCutoffTriadicData M L
      (translatePotentialSample z omega)).onCube R |>.isSymmetric)
    hs0 hsigma
  change ENNReal.ofReal _ ≤ paperHomogenizationError
    (originCube d (m : ℤ)) (m : ℤ) s .infinity (.finite 2)
      (aCutoffFamily M L (translatePotentialSample z omega))
      (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) at hraw
  rw [paperHomogenizationError_eq_ofReal_section6HomogenizationError_of_goodEvent
    M hsLower hsUpper hmL omega z hgood] at hraw
  exact (ENNReal.ofReal_le_ofReal_iff
    (ENNReal.toReal_nonneg : 0 ≤ section6HomogenizationError M s L m omega z)).mp hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
