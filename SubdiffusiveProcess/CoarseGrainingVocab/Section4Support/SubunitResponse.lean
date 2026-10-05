module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.ResponseLocalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge

@[expose] public section

/-!
# Section 4 support: direct subunit response

This is the deterministic half of `e.direct.J.bound.subunit`.  The existing
scalar ratio-energy comparison is reused; this file only packages the paper's
tail-average normalizer and verifies its positivity and integrability.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book

noncomputable section

/-- Every normalized tail-coefficient cube average is strictly positive. -/
theorem tailCoefficientCubeAverage_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 < tailCoefficientCubeAverage M L m ω := by
  have hhom : 0 < ahom M (min m L) := by
    exact (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M (min m L))
  have h := tailAverage_cube_pos_of_ahom_pos M L m ω (m : ℤ) hhom
  simpa [tailAverage, tailCoefficientCubeAverage, cube,
    Ch02.average, volumeAverage, Ch02.cubeDomain_coe] using h

/-- The source-exact direct response bound with the actual tail-average
normalizer. -/
theorem paperScalarProbeMaxOn_cutoff_le_tail_ratio_energy
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (U : Ch02.Domain d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    paperScalarProbeMaxOn U (aCutoffCoeffOnData M L omega U).toCoeffOn
        (tailCoefficientCubeAverage M L m omega) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * Ch02.average U (fun x =>
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
            tailCoefficientCubeAverage M L m omega +
          tailCoefficientCubeAverage M L m omega /
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega x - 2)) := by
  exact paperScalarProbeMaxOn_le_half_scalar_ratio U
    (aCutoffCoeffOnData M L omega U)
    (tailCoefficientCubeAverage_pos M L m omega)
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega)

/-- The source's direct response bound with the actual tail-average
normalizer.  The paper states the comparable right side
`1/2 average (a/b+b/a-2)`; the squared-ratio form below is the immediately
following elementary enlargement used by its moment proof. -/
theorem paperScalarProbeMaxOn_cutoff_le_tail_ratio_squared_energy
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (U : Ch02.Domain d) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    paperScalarProbeMaxOn U (aCutoffCoeffOnData M L ω U).toCoeffOn
        (tailCoefficientCubeAverage M L m ω) ≤
      ENNReal.ofReal (Ch02.average U (fun x =>
        (_root_.SubdiffusiveProcess.Model.aCutoff M L ω x /
            tailCoefficientCubeAverage M L m ω - 1) ^ 2 +
          (tailCoefficientCubeAverage M L m ω /
            _root_.SubdiffusiveProcess.Model.aCutoff M L ω x - 1) ^ 2)) := by
  let a : Vec d → ℝ := _root_.SubdiffusiveProcess.Model.aCutoff M L ω
  let b : ℝ := tailCoefficientCubeAverage M L m ω
  let ha : ScalarCoeffOnData U a := aCutoffCoeffOnData M L ω U
  have hb : 0 < b := tailCoefficientCubeAverage_pos M L m ω
  have ha_pos : ∀ x, 0 < a x :=
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M L ω
  have hcontinuous : Continuous (fun x =>
      (a x / b - 1) ^ 2 + (b / a x - 1) ^ 2) := by
    exact ((((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L ω).div_const _).sub
      continuous_const).pow 2).add
      (((continuous_const.div
        (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L ω)
        (fun x => (ha_pos x).ne')).sub continuous_const).pow 2)
  have hint : IntegrableOn (fun x =>
      (a x / b - 1) ^ 2 + (b / a x - 1) ^ 2)
      (U : Set (Vec d)) :=
    (hcontinuous.continuousOn.integrableOn_compact
      U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set
        subset_closure
  simpa [a, b, ha] using
    paperScalarProbeMaxOn_le_scalar_ratio_energy U ha hb ha_pos hint

end

end SubdiffusiveProcess.CoarseGrainingVocab
