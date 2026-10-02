import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.CoefficientRatio
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ParentTailRatio

/-!
# Hölder Step 3: passing pointwise coefficient ratios to cube averages

The manuscript obtains the comparison of the lower local normalizer with the
top normalizer by bounding the positive coefficient ratio pointwise and then
averaging.  The reverse comparison is not Jensen: its pointwise reciprocal
bound is first cross-multiplied and only then averaged.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

noncomputable section

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- A two-sided pointwise comparison with a positive constant passes to the
average of a positive continuous function on a paper cube. -/
theorem cubeAverage_ratio_bounds_of_pointwise {d : ℕ} (Q : Ch02.Domain d)
    (f : Vec d → ℝ) (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    {b E : ℝ} (havgpos : 0 < Ch02.average Q f)
    (hforward : ∀ x ∈ (Q : Set (Vec d)), f x / b ≤ E)
    (hreverse : ∀ x ∈ (Q : Set (Vec d)), b / f x ≤ E) :
    Ch02.average Q f / b ≤ E ∧ b / Ch02.average Q f ≤ E := by
  have hvolpos : 0 < (volume (Q : Set (Vec d))).toReal := by
    apply ENNReal.toReal_pos
    · exact (Q.isOpen.measure_pos volume Q.nonempty).ne'
    · exact ne_of_lt Q.isDomain.volume_lt_top
  have hvol : (volume (Q : Set (Vec d))).toReal ≠ 0 := hvolpos.ne'
  have hfint : IntegrableOn f (Q : Set (Vec d)) :=
    (hf.continuousOn.integrableOn_compact
      Q.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  have hscaled : IntegrableOn (fun x => f x / b) (Q : Set (Vec d)) := by
    simpa [div_eq_mul_inv, mul_comm] using hfint.const_mul b⁻¹
  have havgForward : Ch02.average Q (fun x => f x / b) ≤ E :=
    volumeAverage_le_of_le_on Q.measurableSet hscaled hvol hforward
  have havgForwardEq : Ch02.average Q (fun x => f x / b) = Ch02.average Q f / b := by
    change volumeAverage (Q : Set (Vec d)) (fun x => f x / b) = _
    rw [show (fun x => f x / b) = b⁻¹ • f by
      funext x
      simp [smul_eq_mul, div_eq_mul_inv, mul_comm], volumeAverage_smul]
    change b⁻¹ * volumeAverage (Q : Set (Vec d)) f =
      volumeAverage (Q : Set (Vec d)) f / b
    ring
  have hcross : ∀ x ∈ (Q : Set (Vec d)), b ≤ E * f x := by
    intro x hx
    exact (div_le_iff₀ (hfpos x)).mp (hreverse x hx)
  have hconstInt : IntegrableOn (fun _ : Vec d => b) (Q : Set (Vec d)) :=
    integrable_const b
  have hEint : IntegrableOn (fun x => E * f x) (Q : Set (Vec d)) :=
    hfint.const_mul E
  have hdiffInt : IntegrableOn (fun x => b - E * f x) (Q : Set (Vec d)) :=
    hconstInt.sub hEint
  have havgCross : Ch02.average Q (fun x => b - E * f x) ≤ 0 :=
    volumeAverage_le_of_le_on Q.measurableSet hdiffInt hvol
      (fun x hx => sub_nonpos.mpr (hcross x hx))
  have hb_le : b ≤ E * Ch02.average Q f := by
    change volumeAverage (Q : Set (Vec d)) (fun x => b - E * f x) ≤ 0 at havgCross
    rw [show (fun x => b - E * f x) =
        (fun _ : Vec d => b) - (fun x => E * f x) by rfl,
      volumeAverage_sub hconstInt hEint, volumeAverage_const hvol,
      show (fun x => E * f x) = E • f by funext x; simp [smul_eq_mul],
      volumeAverage_smul] at havgCross
    exact sub_nonpos.mp havgCross
  constructor
  · rwa [havgForwardEq] at havgForward
  · exact (div_le_iff₀ havgpos).2 hb_le

/-- Pointwise bounds for the exact combined coefficient ratio pass to the
literal translated lower-scale `tailAverage`. -/
theorem tailAverage_ratio_bounds_of_combined {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m q : ℕ}
    (hqm : q ≤ m) (hmL : m ≤ L) (omega : Sample d) (z : Vec d) {E : ℝ}
    (hforward : ∀ x ∈ cube d (q : ℤ),
      combinedCoefficientRatio M L m q omega z x ≤ E)
    (hreverse : ∀ x ∈ cube d (q : ℤ),
      combinedCoefficientRatioInv M L m q omega z x ≤ E) :
    tailAverage M L q omega (translatedCube d (q : ℤ) z) /
        tailCoefficientCubeAverage M L m omega ≤ E ∧
      tailCoefficientCubeAverage M L m omega /
        tailAverage M L q omega (translatedCube d (q : ℤ) z) ≤ E := by
  let f : Vec d → ℝ := tailCoefficient M L q (translatePotentialSample z omega)
  have hf : Continuous f := continuous_tailCoefficient M L q _
  have hfpos : ∀ x, 0 < f x := fun x =>
    tailCoefficient_pos_of_ahom_pos M L q _ (ahom_pos M (min q L)) x
  have hpointForward : ∀ x ∈ cube d (q : ℤ),
      f x / tailCoefficientCubeAverage M L m omega ≤ E := by
    intro x hx
    rw [tailCoefficient_div_eq_combinedCoefficientRatio M hqm hmL omega z x]
    exact hforward x hx
  have hpointReverse : ∀ x ∈ cube d (q : ℤ),
      tailCoefficientCubeAverage M L m omega / f x ≤ E := by
    intro x hx
    rw [tailCoefficientCubeAverage_div_eq_combinedCoefficientRatioInv
      M hqm hmL omega z x]
    exact hreverse x hx
  have h := cubeAverage_ratio_bounds_of_pointwise
    (Ch02.cubeDomain (originCube d (q : ℤ)))
    f hf hfpos (tailCoefficientCubeAverage_pos M L q _) hpointForward hpointReverse
  change tailCoefficientCubeAverage M L q (translatePotentialSample z omega) /
      tailCoefficientCubeAverage M L m omega ≤ E ∧
    tailCoefficientCubeAverage M L m omega /
      tailCoefficientCubeAverage M L q (translatePotentialSample z omega) ≤ E at h
  rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
  simpa only [f] using h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
